use std::{marker::PhantomData, ops::Rem};

use bellperson::{LinearCombination, SynthesisError, ConstraintSystem};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::{BigInt, Sign, BigUint};
use num_traits::{Zero, One};

use crate::{params::EmulatedFieldParams, util::{range_check_constant, range_check_lc, mul_lc_with_scalar}};

#[derive(Debug, Clone)]
pub struct AllocatedLimbs<F: PrimeField + PrimeFieldBits> {
    limbs: Vec<LinearCombination<F>>,
    limb_values: Option<Vec<F>>,
}

#[derive(Debug, Clone)]
pub enum EmulatedLimbs<F: PrimeField + PrimeFieldBits> {
    Allocated(AllocatedLimbs<F>),
    Constant(Vec<F>),
}

pub struct EmulatedFieldElement<F: PrimeField + PrimeFieldBits, P: EmulatedFieldParams> {
    limbs: EmulatedLimbs<F>,
    overflow: usize,
    internal: bool,
    marker: PhantomData<P>,
}

impl<F, P> From<&BigInt> for EmulatedFieldElement<F, P>
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams,
{
    fn from(value: &BigInt) -> Self {
        let mut v = value.clone();
        assert!(v.sign() != Sign::Minus);

        if v > P::modulus() {
            v = v.rem(P::modulus());
        }

        assert!(v.bits() <= (P::num_limbs()*P::bits_per_limb()) as u64);
        let mut v_bits: Vec<bool> = vec![false; P::num_limbs()*P::bits_per_limb()];

        let v_bytes = v.to_biguint().and_then(|w| Some(w.to_bytes_le())).unwrap();
        for (i, b) in v_bytes.into_iter().enumerate() {
            for j in 0..8usize {
                if b & (1u8 << j) != 0 {
                    v_bits[i*8 + j] = true;
                }
            }
        }
        
        let mut limbs = vec![F::zero(); P::num_limbs()];
        for i in 0..P::num_limbs() {
            let mut coeff = F::one();
            for j in 0..P::bits_per_limb() {
                if v_bits[i*P::bits_per_limb() + j] {
                    limbs[i] += coeff
                }
                coeff = coeff.double();
            }
        }

        Self {
            limbs: EmulatedLimbs::Constant(limbs),
            overflow: 0,
            internal: true,
            marker: PhantomData,
        }
    }
}

impl<F, P> From<&EmulatedFieldElement<F, P>> for BigInt
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams,
{
    fn from(value: &EmulatedFieldElement<F, P>) -> Self {
        let mut res: BigUint = Zero::zero();
        let one: &BigUint = &One::one();
        let mut base: BigUint = one.clone();
        let limbs = match &value.limbs {
            EmulatedLimbs::Allocated(x) => x.limb_values.as_ref().unwrap(),
            EmulatedLimbs::Constant(x) => x,
        };
        for i in 0..P::num_limbs() {
            res += base.clone() * BigUint::from_bytes_le(limbs[i].to_repr().as_ref());
            base = base * (one << P::bits_per_limb())
        }
        BigInt::from(res)
    }

}

impl<F, P> EmulatedFieldElement<F, P>
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams,
{
    fn new_internal_element(
        limbs: EmulatedLimbs<F>,
        overflow: usize,
    ) -> Self {
        Self {
            limbs,
            overflow,
            internal: true,
            marker: PhantomData,
        }
    }

    /// Enforces limb bit widths in a [EmulatedFieldElement]
    /// 
    /// All the limbs are constrained to have width that is at most equal to the width
    /// specified by [EmulatedFieldParams].
    /// If `modulus_width` is `true`, the most significant limb will be constrained to have
    /// width less than or equal to the most significant limb of the modulus.
    fn enforce_width<CS>(
        &self,
        cs: &mut CS,
        modulus_width: bool,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if let EmulatedLimbs::Constant(limb_values) = &self.limbs {
            if limb_values.len() != P::num_limbs() {
                eprintln!("Constant limb count does not match required count");
                return Err(SynthesisError::Unsatisfiable);
            }

            for i in 0..P::num_limbs() {
                let mut required_bit_width = P::bits_per_limb();
                if modulus_width && i == P::num_limbs() - 1 {
                    required_bit_width = (P::modulus().bits() as usize - 1) % P::bits_per_limb() + 1;
                }
                range_check_constant(limb_values[i], required_bit_width)?;
            }
        }
        if let EmulatedLimbs::Allocated(allocated_limbs) = &self.limbs {
            if allocated_limbs.limbs.len() != allocated_limbs.limb_values.as_ref().map(|v| v.len()).unwrap() {
                eprintln!("Limb counts in LCs and values do not match");
                return Err(SynthesisError::Unsatisfiable);
            }

            if modulus_width && allocated_limbs.limbs.len() != P::num_limbs() {
                eprintln!("LC limb count does not match required count");
                return Err(SynthesisError::Unsatisfiable);
            }
            
            let limb_values = allocated_limbs.limb_values.as_ref().unwrap();
            
            for i in 0..P::num_limbs() {
                let mut required_bit_width = P::bits_per_limb();
                if modulus_width && i == P::num_limbs() - 1 {
                    required_bit_width = (P::modulus().bits() as usize - 1) % P::bits_per_limb() + 1;
                }

                range_check_lc(
                    &mut cs.namespace(|| format!("range check limb {i}")),
                    &allocated_limbs.limbs[i],
                    limb_values[i],
                    required_bit_width
                )?;
            }
        }
        Ok(())
    }

    /// Enforces limb bit widths in a [EmulatedFieldElement] if it is not an
    /// internal element or a constant
    fn enforce_width_conditional<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<bool, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if self.internal {
            return Ok(false);
        }
        if let EmulatedLimbs::Constant(_) = self.limbs {
            return Ok(false);
        }
        self.enforce_width(&mut cs.namespace(|| "enforce width"), true)?;
        Ok(true)
    }

    /// Constructs a [EmulatedFieldElement] from limbs of type [EmulatedLimbs].
    /// The method name is inherited from gnark.
    /// 
    /// All the limbs are constrained to have width that is at most equal to the width
    /// specified by [EmulatedFieldParams].
    /// If `strict` is `true`, the most significant limb will be constrained to have
    /// width less than or equal to the most significant limb of the modulus.
    fn pack_limbs<CS>(
        cs: &mut CS,
        limbs: EmulatedLimbs<F>,
        strict: bool,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let elem = Self::new_internal_element(limbs, 0);
        elem.enforce_width(&mut cs.namespace(|| "pack limbs"), strict)?;
        Ok(elem)
    }

    fn compact_limbs<CS>(
        &self,
        cs: &mut CS,
        group_size: usize,
        new_bits_per_limb: usize,
    ) -> Result<EmulatedLimbs<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if P::bits_per_limb() == new_bits_per_limb {
            return Ok(self.limbs.clone());
        }
        if let EmulatedLimbs::Constant(_) = self.limbs {
            eprintln!("compact_limbs not implemented for constants");
            return Err(SynthesisError::Unsatisfiable);
        }

        if let EmulatedLimbs::<F>::Allocated(allocated_limbs) = &self.limbs {
            if allocated_limbs.limbs.len() != allocated_limbs.limb_values.as_ref().map(|v| v.len()).unwrap() {
                eprintln!("Limb counts in LCs and values do not match");
                return Err(SynthesisError::Unsatisfiable);
            }

            let mut coeffs = vec![F::zero(); group_size];
            for i in 0..group_size {
                let mut tmp = F::one();
                coeffs[i] = tmp;
                for _j in 0..P::bits_per_limb() {
                    tmp = tmp.double();
                }
            }
            
            let new_num_limbs = (P::num_limbs() + group_size - 1)/group_size;
            let mut res = vec![LinearCombination::<F>::zero(); new_num_limbs];
            let mut res_values = vec![F::zero(); new_num_limbs];

            for i in 0..new_num_limbs {
                for j in 0..group_size {
                    if i*group_size + j < allocated_limbs.limbs.len() {
                        res[i] = mul_lc_with_scalar(allocated_limbs.limbs[i*group_size+j].clone(), coeffs[j]) + &res[i];
                        res_values[i] += allocated_limbs.limb_values.as_ref().unwrap()[i*group_size+j] * coeffs[j];
                    }
                }
            }
            return Ok(EmulatedLimbs::Allocated(AllocatedLimbs { limbs: res, limb_values: Some(res_values) }));
        }
        // Should not reach this line
        return Err(SynthesisError::Unsatisfiable);
    }

    fn compact<CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
    ) -> Result<(EmulatedLimbs<F>, EmulatedLimbs<F>, usize), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let max_overflow = a.overflow.max(b.overflow);
        // Substract one bit to account for overflow due to grouping in compact_limbs
        let max_num_bits = F::CAPACITY as usize - 1 - max_overflow;
        let group_size = max_num_bits / P::bits_per_limb();

        if group_size == 0 {
            // No space for compacting
            return Ok((a.limbs.clone(), b.limbs.clone(), P::bits_per_limb()));
        }

        let new_bits_per_limb = P::bits_per_limb() * group_size;
        let a_compact = a.compact_limbs(
            &mut cs.namespace(|| "compact a limbs"),
            group_size,
            new_bits_per_limb
        )?;
        let b_compact = b.compact_limbs(
            &mut cs.namespace(|| "compact b limbs"),
            group_size,
            new_bits_per_limb
        )?;

        return Ok((a_compact, b_compact, new_bits_per_limb));
    }
}


use std::ops::Div;
use std::{marker::PhantomData, ops::Rem};

use bellperson::{LinearCombination, SynthesisError, ConstraintSystem};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::{BigInt, Sign, BigUint};
use num_traits::{Zero, One};

use crate::util::{range_check_constant, range_check_lc, mul_lc_with_scalar, decompose, bigint_to_scalar};
use crate::params::EmulatedFieldParams;

#[derive(Clone)]
pub struct AllocatedLimbs<F: PrimeField + PrimeFieldBits> {
    pub(crate) limbs: Vec<LinearCombination<F>>,
    pub(crate) limb_values: Option<Vec<F>>,
}

pub enum EmulatedLimbs<F: PrimeField + PrimeFieldBits> {
    Allocated(AllocatedLimbs<F>),
    Constant(Vec<F>),
}

impl<F> From<Vec<F>> for EmulatedLimbs<F>
where
    F: PrimeField + PrimeFieldBits
{
    fn from(value: Vec<F>) -> Self {
        EmulatedLimbs::Constant(value)
    }
}

impl<F> AsRef<EmulatedLimbs<F>> for EmulatedLimbs<F>
where
    F: PrimeField + PrimeFieldBits
{
    fn as_ref(&self) -> &EmulatedLimbs<F> {
        self
    }
}

impl<F: PrimeField + PrimeFieldBits> Clone for EmulatedLimbs<F> {
    fn clone(&self) -> Self {
        match self {
            Self::Allocated(a) => Self::Allocated(a.clone()),
            Self::Constant(c) => Self::Constant(c.clone()),
        }
    }
}

pub struct EmulatedFieldElement<F: PrimeField + PrimeFieldBits, P: EmulatedFieldParams> {
    pub(crate) limbs: EmulatedLimbs<F>,
    pub(crate) overflow: usize,
    pub(crate) internal: bool,
    marker: PhantomData<P>,
}

impl<F, P> Clone for EmulatedFieldElement<F, P>
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams,
{
    fn clone(&self) -> Self {
        Self {
            limbs: self.limbs.clone(),
            overflow: self.overflow.clone(),
            internal: self.internal.clone(),
            marker: self.marker.clone(),
        }
    }
}

impl<F, P> From<&BigInt> for EmulatedFieldElement<F, P>
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams,
{
    /// Converts a [BigInt] into an [EmulatedFieldElement]
    /// 
    /// Note that any [BigInt] larger than the field modulus is
    /// first reduced. A [BigInt] equal to the modulus itself is not
    /// reduced.
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
    pub fn new_internal_element(
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

    pub fn len(&self) -> usize {
        match self.limbs.as_ref() {
            // TODO: Check that the lengths of allocated_limbs.limbs and allocated_limbs.limb_values match
            EmulatedLimbs::Allocated(allocated_limbs) => allocated_limbs.limbs.len(),
            EmulatedLimbs::Constant(constant_limbs) => constant_limbs.len(),
        }
    }

    pub fn is_constant(
        &self,
    ) -> bool {
        if let EmulatedLimbs::Constant(_) = self.limbs {
            true
        } else {
            false
        }
    }

    pub fn allocate_limbs<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<EmulatedLimbs<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if let EmulatedLimbs::Constant(limb_values) = &self.limbs {
            let mut lc_vec: Vec<LinearCombination<F>> = vec![];

            for (i, v) in limb_values.into_iter().enumerate() {
                let allocated_limb = cs.alloc(
                    || format!("allocating limb {i}"),
                    || Ok(*v),
                )?;
                lc_vec.push(LinearCombination::zero() + allocated_limb);
            }
            
            let allocated_limbs = AllocatedLimbs {
                limbs: lc_vec,
                limb_values: Some(limb_values.clone()),
            };
            
            Ok(EmulatedLimbs::Allocated(allocated_limbs))
        } else {
            eprintln!("input must have constant limb values");
            Err(SynthesisError::Unsatisfiable)
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
    pub fn enforce_width_conditional<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<bool, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if self.internal {
            return Ok(false);
        }
        if self.is_constant() {
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

    pub fn compact_limbs(
        &self,
        group_size: usize,
        new_bits_per_limb: usize,
    ) -> Result<EmulatedLimbs<F>, SynthesisError> {
        if P::bits_per_limb() == new_bits_per_limb {
            return Ok(self.limbs.clone());
        }
        if self.is_constant() {
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
                        res[i] = mul_lc_with_scalar(&allocated_limbs.limbs[i*group_size+j], &coeffs[j]) + &res[i];
                        res_values[i] += allocated_limbs.limb_values.as_ref().unwrap()[i*group_size+j] * coeffs[j];
                    }
                }
            }
            return Ok(EmulatedLimbs::Allocated(AllocatedLimbs { limbs: res, limb_values: Some(res_values) }));
        }
        // Should not reach this line
        return Err(SynthesisError::Unsatisfiable);
    }

    /// Computes the remainder modulo the field modulus
    pub fn compute_rem<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a_int: BigInt = self.into();
        let p = P::modulus();
        let r_int = a_int.rem(p);
        let r_value = Self::from(&r_int);

        let res_limbs = r_value.allocate_limbs(
            &mut cs.namespace(|| "allocate from remainder value")
        )?;

        let res = Self::pack_limbs(
            &mut cs.namespace(|| "enforce bitwidths on remainder"),
            res_limbs,
            true,
        )?;
        Ok(res)
    }

    /// Computes the remainder modulo the field modulus
    pub fn compute_quotient<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // TODO: Check the need for the "+ 1"
        let num_res_limbs = (self.len()*P::bits_per_limb() + self.overflow + 1
            - (P::modulus().bits() as usize)    // Deduct the modulus bit size
            + P::bits_per_limb() - 1) /         // This term is to round up to next integer
            P::bits_per_limb();

        let a_int: BigInt = self.into();
        let p = P::modulus();
        let k_int = a_int.div(p);
        let k_int_limbs = decompose(&k_int, P::bits_per_limb(), num_res_limbs)?;

        let res_limbs = k_int_limbs
            .into_iter()
            .map(|i| bigint_to_scalar(i))
            .collect::<Vec<F>>()
            .into();

        let res = Self::pack_limbs(
            &mut cs.namespace(|| "enforce bitwidths on quotient"),
            res_limbs,
            true,
        )?;
        Ok(res)
    }

}


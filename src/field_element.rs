use std::{marker::PhantomData, ops::Rem};

use bellperson::{LinearCombination, SynthesisError, ConstraintSystem};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::{BigInt, Sign, BigUint};
use num_traits::{Zero, One};

use crate::util::{range_check_constant, range_check_lc, mul_lc_with_scalar};

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

impl<F> EmulatedLimbs<F>
where
    F: PrimeField + PrimeFieldBits
{
    pub(crate) fn allocate_limbs<CS>(
        cs: &mut CS,
        limb_values: &Vec<F>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
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
    }
}

/// Emulated field is assumed to be prime. So inverses always
/// exist for non-zero field elements
pub trait EmulatedFieldParams {
    fn num_limbs() -> usize;
    fn bits_per_limb() -> usize;
    fn modulus() -> BigInt;
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
        for i in 0..limbs.len() {
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
    pub fn zero() -> EmulatedFieldElement<F, P> {
        EmulatedFieldElement::<F, P>::from(&BigInt::from(0))
    }

    pub fn one() -> EmulatedFieldElement<F, P> {
        EmulatedFieldElement::<F, P>::from(&BigInt::from(1))
    }

    pub fn modulus() -> EmulatedFieldElement<F, P> {
        EmulatedFieldElement::<F, P>::from(&P::modulus())
    }

    pub fn max_overflow() -> usize {
        F::CAPACITY as usize - P::bits_per_limb()
    }

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
            EmulatedLimbs::<F>::allocate_limbs(
                &mut cs.namespace(|| "allocate variables from constant limbs"),
                limb_values
            )
        } else {
            eprintln!("input must have constant limb values");
            Err(SynthesisError::Unsatisfiable)
        }
    }

    pub fn allocate_field_element<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if self.is_constant() {
            let allocated_limbs = self.allocate_limbs(
                &mut cs.namespace(|| "allocate variables from constant limbs"),
            )?;
            let allocated_field_element = Self::pack_limbs(
                &mut cs.namespace(|| "check limb bitwidths"),
                allocated_limbs,
                true,
            )?;
            Ok(allocated_field_element)
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
            
            for i in 0..allocated_limbs.limbs.len() {
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
    pub(crate) fn enforce_width_conditional<CS>(
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
    pub(crate) fn pack_limbs<CS>(
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
            let mut tmp = F::one();
            for i in 0..group_size {
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

}

#[cfg(test)]
mod tests {
    use bellperson::gadgets::test::TestConstraintSystem;
    use num_bigint::RandBigInt;

    use super::*;
    use pasta_curves::Fp;

    struct Ed25519Fp;

    impl EmulatedFieldParams for Ed25519Fp {
        fn num_limbs() -> usize {
            5
        }

        fn bits_per_limb() -> usize {
            51
        }

        fn modulus() -> BigInt {
            BigInt::parse_bytes(b"7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed", 16).unwrap()
        }
    } 

    #[test]
    fn test_add() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let zero_int = BigInt::from(0);
        let a_int = rng.gen_bigint_range(&zero_int, &Ed25519Fp::modulus());
        let b_int = rng.gen_bigint_range(&zero_int, &Ed25519Fp::modulus());
        let sum_int = (&a_int + &b_int).rem(&Ed25519Fp::modulus());

        let a_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&a_int);
        let b_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&b_int);
        let sum_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&sum_int);

        let a = a_const.allocate_field_element(&mut cs.namespace(|| "a"));
        let b = b_const.allocate_field_element(&mut cs.namespace(|| "b"));
        let sum = sum_const.allocate_field_element(&mut cs.namespace(|| "sum"));
        assert!(a.is_ok());
        assert!(b.is_ok());
        assert!(sum.is_ok());
        let a = a.unwrap();
        let b = b.unwrap();
        let sum = sum.unwrap();


        let sum_calc = a.add(&mut cs.namespace(|| "a + b"), &b);
        assert!(sum_calc.is_ok());
        let sum_calc = sum_calc.unwrap();

        let res = EmulatedFieldElement::<Fp, Ed25519Fp>::assert_is_equal(
            &mut cs.namespace(|| "check equality"),
            &sum_calc,
            &sum,
        );
        assert!(res.is_ok());

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
        println!("Number of constraints = {:?}", cs.num_constraints());
    }

}
use std::{marker::PhantomData, ops::Rem};

use bellperson::{LinearCombination, SynthesisError, ConstraintSystem, gadgets::boolean::AllocatedBit};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::{BigInt, BigUint};
use num_traits::{Zero, One, Signed};

use crate::util::*;

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

/// Parameters of a prime of the form `2^e-c`
pub struct PseudoMersennePrime {
    pub e: u32,
    pub c: BigInt,
}

/// Emulated field is assumed to be prime. So inverses always
/// exist for non-zero field elements
pub trait EmulatedFieldParams {
    fn num_limbs() -> usize;
    fn bits_per_limb() -> usize;
    fn modulus() -> BigInt;
    
    fn is_modulus_pseudo_mersenne() -> bool {
        false
    }
    
    fn pseudo_mersenne_params() -> Option<PseudoMersennePrime> {
        None
    }
}

pub struct EmulatedFieldElement<F: PrimeField + PrimeFieldBits, P: EmulatedFieldParams> {
    pub(crate) limbs: EmulatedLimbs<F>,
    pub(crate) overflow: usize,
    pub(crate) internal: bool,
    pub(crate) marker: PhantomData<P>,
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
        assert!(!v.is_negative());

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
        EmulatedFieldElement::<F, P>::from(&BigInt::zero())
    }

    pub fn one() -> EmulatedFieldElement<F, P> {
        EmulatedFieldElement::<F, P>::from(&BigInt::one())
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

    /// Allocates an emulated field element from constant limbs **without**
    /// in-circuit checks for field membership. If you want to enforce membership
    /// in the field, you can call `check_field_membership` on the output of this
    /// method.
    /// 
    /// This method is suitable for allocating field elements from public inputs
    /// that are known to be in the field.
    pub fn allocate_field_element_unchecked<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if self.is_constant() {
            // Below statement does not perform a in-circuit check as the input is a constant
            self.check_field_membership(&mut cs.namespace(|| "check field membership of constant input"))?;

            let allocated_limbs = self.allocate_limbs(
                &mut cs.namespace(|| "allocate variables from constant limbs"),
            )?;

            let allocated_field_element = Self::new_internal_element(allocated_limbs, 0);
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
    /// For constant elements, the number of limbs is required to be equal to P::num_limbs().
    /// For allocated elements, the number of limbs is required to be equal to P::num_limbs()
    /// only if `modulus_width` is true. In the calculation of quotients, the limbs may not
    /// be equal to P::num_limbs()
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
    /// 
    /// The number of limbs is required to be equal to P::num_limbs(), and
    /// the most significant limb will be constrained to have
    /// width less than or equal to the most significant limb of the modulus.
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
            for i in 0..group_size {
                coeffs[i] = bigint_to_scalar(&(BigInt::one() << P::bits_per_limb() * i));
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

    pub fn check_field_membership<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if self.is_constant() {
            if BigInt::from(self) < P::modulus() {
                return Ok(());
            }
            else {
                return Err(SynthesisError::Unsatisfiable);
            }
        }

        if self.len() != P::num_limbs() {
            eprintln!("Field membership check only implemented for limb count equal to default");
            return Err(SynthesisError::Unsatisfiable);
        }

        match &self.limbs {
            EmulatedLimbs::Allocated(var) => {
                let var_limb_values = var.limb_values.clone().unwrap();
                // Number of modulus bits in most significant limb
                let num_mod_bits_in_msl = P::modulus().bits() as usize - (P::num_limbs()-1)*P::bits_per_limb();

                for i in 0..P::num_limbs() {
                    let num_bits = if i == P::num_limbs() - 1 {
                        num_mod_bits_in_msl
                    } else {
                        P::bits_per_limb()
                    };

                    range_check_lc(
                        &mut cs.namespace(|| format!("range check limb {i}")),
                        &var.limbs[i],
                        var_limb_values[i],
                        num_bits,
                    )?;
                }

                if P::is_modulus_pseudo_mersenne() {
                    let pseudo_mersenne_params = P::pseudo_mersenne_params().unwrap();
                    // Maximum value of most significant limb
                    let max_msl_value = (BigInt::one() << num_mod_bits_in_msl)- BigInt::one();
                    // Maximum value of least significant limbs
                    let max_lsl_value = (BigInt::one() << P::bits_per_limb()) - BigInt::one();

                    let equality_bits: Vec<AllocatedBit> = (1..P::num_limbs())
                        .map( |i| {
                            let max_limb_value = if i == P::num_limbs() - 1 {
                                bigint_to_scalar(&max_msl_value)
                            } else {
                                bigint_to_scalar(&max_lsl_value)
                            };
            
                            let bit = alloc_lc_equals_constant(
                                cs.namespace(|| format!("limb {i} equals max value")),
                                &var.limbs[i],
                                var_limb_values[i],
                                max_limb_value,
                            );
                            bit.unwrap()
                        })
                        .collect();

                    let mut kary_and = equality_bits[0].clone();
                    for i in 1..P::num_limbs()-1 {
                        kary_and = AllocatedBit::and(
                            cs.namespace(|| format!("and of bits {} and {}", i-1, i)),
                            &kary_and,
                            &equality_bits[i],
                        )?
                    }

                    let c = bigint_to_scalar(&pseudo_mersenne_params.c);

                    // Least significant limb increased by c if all the most significant limbs are maxxed out
                    // If kary_and is true, then lsl_lc = var.limbs[0] + c. Otherwise, lsl_lc = var.limbs[0].
                    // The latter is already within P::bits_per_limb(). If the former only has P::bits_per_limb(),
                    // then var.limbs[0] is at most 2^(P::bits_per_limb())-1-c
                    let lsl_lc = var.limbs[0].clone() + (c, kary_and.get_variable());
                    let lsl_lc_value = if kary_and.get_value().unwrap() {
                        var_limb_values[0] + c
                    } else {
                        var_limb_values[0]
                    };
                    range_check_lc(
                        &mut cs.namespace(|| format!("range check limb least significant limb + possibly c")),
                        &lsl_lc,
                        lsl_lc_value,
                        P::bits_per_limb(),
                    )?;

                } else {
                    panic!("Check field membership implemented only for pseudo-Mersenne prime moduli");
                }
            },
            EmulatedLimbs::Constant(_) => panic!("constant case is already handled; this code should be unreachable"),
        }

        Ok(())
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

        fn is_modulus_pseudo_mersenne() -> bool {
            true
        }

        fn pseudo_mersenne_params() -> Option<PseudoMersennePrime> {
            Some(PseudoMersennePrime {
                e: 255,
                c: BigInt::from(19),
            })
        }
    } 

    #[test]
    fn test_add() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let a_int = rng.gen_bigint_range(&BigInt::zero(), &Ed25519Fp::modulus());
        let b_int = rng.gen_bigint_range(&BigInt::zero(), &Ed25519Fp::modulus());
        let sum_int = (&a_int + &b_int).rem(&Ed25519Fp::modulus());

        let a_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&a_int);
        let b_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&b_int);
        let sum_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&sum_int);

        let a = a_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
        let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
        let sum = sum_const.allocate_field_element_unchecked(&mut cs.namespace(|| "sum"));
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

    #[test]
    fn test_sub() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let tmp1 = rng.gen_bigint_range(&BigInt::zero(), &Ed25519Fp::modulus());
        let tmp2 = rng.gen_bigint_range(&BigInt::zero(), &Ed25519Fp::modulus());
        let a_int = (&tmp1).max(&tmp2);
        let b_int = (&tmp1).min(&tmp2);
        let diff_int = (a_int - b_int).rem(&Ed25519Fp::modulus());

        let a_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(a_int);
        let b_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(b_int);
        let diff_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&diff_int);

        let a = a_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
        let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
        let diff = diff_const.allocate_field_element_unchecked(&mut cs.namespace(|| "diff"));
        assert!(a.is_ok());
        assert!(b.is_ok());
        assert!(diff.is_ok());
        let a = a.unwrap();
        let b = b.unwrap();
        let diff = diff.unwrap();


        let diff_calc = a.sub(&mut cs.namespace(|| "a - b"), &b);
        assert!(diff_calc.is_ok());
        let diff_calc = diff_calc.unwrap();

        let res = EmulatedFieldElement::<Fp, Ed25519Fp>::assert_is_equal(
            &mut cs.namespace(|| "check equality"),
            &diff_calc,
            &diff,
        );
        assert!(res.is_ok());

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
        println!("Number of constraints = {:?}", cs.num_constraints());
    }
    
    #[test]
    fn test_mul() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let a_int = rng.gen_bigint_range(&BigInt::zero(), &Ed25519Fp::modulus());
        let b_int = rng.gen_bigint_range(&BigInt::zero(), &Ed25519Fp::modulus());
        let prod_int = (&a_int * &b_int).rem(&Ed25519Fp::modulus());

        let a_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&a_int);
        let b_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&b_int);
        let prod_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&prod_int);

        let a = a_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
        let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
        let prod = prod_const.allocate_field_element_unchecked(&mut cs.namespace(|| "prod"));
        assert!(a.is_ok());
        assert!(b.is_ok());
        assert!(prod.is_ok());
        let a = a.unwrap();
        let b = b.unwrap();
        let prod = prod.unwrap();


        let prod_calc = a.mul(&mut cs.namespace(|| "a * b"), &b);
        assert!(prod_calc.is_ok());
        let prod_calc = prod_calc.unwrap();

        let res = EmulatedFieldElement::<Fp, Ed25519Fp>::assert_is_equal(
            &mut cs.namespace(|| "check equality"),
            &prod_calc,
            &prod,
        );
        assert!(res.is_ok());

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
        println!("Number of constraints = {:?}", cs.num_constraints());
    }

    #[test]
    fn test_divide() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let a_int = rng.gen_bigint_range(&BigInt::zero(), &Ed25519Fp::modulus());
        let b_int = rng.gen_bigint_range(&BigInt::one(), &Ed25519Fp::modulus());
        let p = Ed25519Fp::modulus();
        let p_minus_2 = &p - BigInt::from(2);
        // b^(p-1) = 1 mod p for non-zero b. So b^(-1) = b^(p-2)
        let b_inv_int = b_int.modpow(&p_minus_2, &p);
        let ratio_int = (&a_int * b_inv_int).rem(&p);

        let a_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&a_int);
        let b_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&b_int);
        let ratio_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&ratio_int);

        let a = a_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
        let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
        let ratio = ratio_const.allocate_field_element_unchecked(&mut cs.namespace(|| "ratio"));
        assert!(a.is_ok());
        assert!(b.is_ok());
        assert!(ratio.is_ok());
        let a = a.unwrap();
        let b = b.unwrap();
        let ratio = ratio.unwrap();


        let ratio_calc = a.divide(&mut cs.namespace(|| "a divided by b"), &b);
        assert!(ratio_calc.is_ok());
        let ratio_calc = ratio_calc.unwrap();

        let res = EmulatedFieldElement::<Fp, Ed25519Fp>::assert_is_equal(
            &mut cs.namespace(|| "check equality"),
            &ratio_calc,
            &ratio,
        );
        assert!(res.is_ok());

        let b_mul_ratio = b.mul(&mut cs.namespace(|| "b * (a div b)"), &ratio);
        assert!(b_mul_ratio.is_ok());
        let b_mul_ratio = b_mul_ratio.unwrap();

        let res = EmulatedFieldElement::<Fp, Ed25519Fp>::assert_is_equal(
            &mut cs.namespace(|| "check equality of a and b * (a div b)"),
            &b_mul_ratio,
            &a,
        );
        assert!(res.is_ok());

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
        println!("Number of constraints = {:?}", cs.num_constraints());
    }

    #[test]
    fn test_inverse() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let b_int = rng.gen_bigint_range(&BigInt::one(), &Ed25519Fp::modulus());
        let p = Ed25519Fp::modulus();
        let p_minus_2 = &p - BigInt::from(2);
        // b^(p-1) = 1 mod p for non-zero b. So b^(-1) = b^(p-2)
        let b_inv_int = (&b_int).modpow(&p_minus_2, &p);

        let b_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&b_int);
        let b_inv_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&b_inv_int);

        let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
        let b_inv = b_inv_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b_inv"));
        assert!(b.is_ok());
        assert!(b_inv.is_ok());
        let b = b.unwrap();
        let b_inv = b_inv.unwrap();


        let b_inv_calc = b.inverse(&mut cs.namespace(|| "b inverse"));
        assert!(b_inv_calc.is_ok());
        let b_inv_calc = b_inv_calc.unwrap();

        let res = EmulatedFieldElement::<Fp, Ed25519Fp>::assert_is_equal(
            &mut cs.namespace(|| "check equality"),
            &b_inv_calc,
            &b_inv,
        );
        assert!(res.is_ok());

        let b_mul_b_inv = b.mul(&mut cs.namespace(|| "b * b_inv"), &b_inv);
        assert!(b_mul_b_inv.is_ok());
        let b_mul_b_inv = b_mul_b_inv.unwrap();

        let res = EmulatedFieldElement::<Fp, Ed25519Fp>::assert_is_equal(
            &mut cs.namespace(|| "check equality one and b * b_inv"),
            &b_mul_b_inv,
            &EmulatedFieldElement::<Fp, Ed25519Fp>::one(),
        );
        assert!(res.is_ok());

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
        println!("Number of constraints = {:?}", cs.num_constraints());
    }

    #[test]
    fn test_field_membership() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let q_int = (BigInt::one() << 255) - BigInt::from(19);
        let mut rng = rand::thread_rng();

        let a_int = rng.gen_bigint_range(&BigInt::zero(), &q_int);
        let a_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&a_int);
        let a = a_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
        println!("Num constraints before field membership check = {:?}", cs.num_constraints());
        assert!(a.is_ok());
        let a = a.unwrap();

        let res = a.check_field_membership(
            &mut cs.namespace(|| "check field membership of random a"),
        );
        assert!(res.is_ok());

        assert!(cs.is_satisfied());
        println!("Num constraints after field membership check = {:?}", cs.num_constraints());

        let b_int = &q_int - BigInt::one();
        let b_const = EmulatedFieldElement::<Fp, Ed25519Fp>::from(&b_int);
        let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "q-1"));
        assert!(b.is_ok());
        let b = b.unwrap();

        let res = b.check_field_membership(
            &mut cs.namespace(|| "check field membership of q-1"),
        );
        assert!(res.is_ok());

        assert!(cs.is_satisfied());

        let one = EmulatedFieldElement::<Fp, Ed25519Fp>::one();
        let q = b.add(&mut cs.namespace(|| "add 1 to q-1"), &one);
        assert!(q.is_ok());
        let q = q.unwrap();

        let res = q.check_field_membership(
            &mut cs.namespace(|| "check field non-membership of q"),
        );
        assert!(res.is_ok());

        assert!(!cs.is_satisfied());

    }

}
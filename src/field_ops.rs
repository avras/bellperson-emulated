use std::{ops::{Rem, Shl}, fmt::Debug};

use bellperson::{SynthesisError, ConstraintSystem, LinearCombination, gadgets::boolean::{Boolean, AllocatedBit}};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::BigInt;

use crate::field_element::{EmulatedFieldElement, EmulatedLimbs, AllocatedLimbs, EmulatedFieldParams};
use crate::util::{recompose, decompose, mul_lc_with_scalar, bigint_to_scalar, Num};

#[derive(Debug, Clone)]
pub enum Optype {
    Add,
    Sub,
    Mul,
    // MulConstant,
}

#[derive(Clone)]
pub struct OverflowError {
    op: Optype,
    next_overflow: usize,
    reduce_right: bool,
}

impl Debug for OverflowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OverflowError")
            .field("op", &self.op)
            .field("next_overflow", &self.next_overflow)
            .field("reduce_right", &self.reduce_right)
            .finish()
    }
}

impl<F, P> EmulatedFieldElement<F, P>
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams,
{
    fn compact(
        a: &Self,
        b: &Self,
    ) -> Result<(EmulatedLimbs<F>, EmulatedLimbs<F>, usize), SynthesisError> {
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
            group_size,
            new_bits_per_limb
        )?;
        let b_compact = b.compact_limbs(
            group_size,
            new_bits_per_limb
        )?;

        return Ok((a_compact, b_compact, new_bits_per_limb));
    }


    /// Asserts that two allocated limbs vectors represent the same integer value.
    /// This is a costly operation as it performs bit decomposition of the limbs.
    fn assert_limbs_equality_slow<CS>(
        cs: &mut CS,
        a: &EmulatedLimbs<F>,
        b: &EmulatedLimbs<F>,
        num_bits_per_limb: usize,
        num_carry_bits: usize,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if let (EmulatedLimbs::Allocated(a_l), EmulatedLimbs::Allocated(b_l)) = (a, b) {
            let num_limbs = a_l.limbs.len().max(b_l.limbs.len());
            let max_value = bigint_to_scalar::<F>(BigInt::from(1).shl(num_bits_per_limb + num_carry_bits));
            let max_value_shift = bigint_to_scalar::<F>(BigInt::from(1).shl(num_carry_bits));

            let mut carry = Num::<F>::zero();
            for i in 0..num_limbs {
                let mut diff_lc = carry.lc(F::one()) + &LinearCombination::from_coeff(CS::one(), max_value);
                let mut diff_val = carry.get_value().unwrap() + max_value;
                if i < a_l.limbs.len() {
                    diff_lc = diff_lc + &a_l.limbs[i];
                    diff_val = diff_val + a_l.limb_values.as_ref().unwrap()[i];
                }
                if i < b_l.limbs.len() {
                    diff_lc = diff_lc - &b_l.limbs[i];
                    diff_val = diff_val - b_l.limb_values.as_ref().unwrap()[i];
                }
                if i > 0 {
                    diff_lc = diff_lc - &LinearCombination::from_coeff(CS::one(), max_value_shift);
                    diff_val = diff_val - max_value_shift;
                }
                
                carry = Self::right_shift(
                    &mut cs.namespace(|| format!("allocated carry {i}")),
                    &Num::new(Some(diff_val), diff_lc),
                    num_bits_per_limb,
                    num_bits_per_limb + num_carry_bits + 1,
                )?;
            }

        } else {
            eprintln!("Both inputs must be allocated limbs, not constants");
            return Err(SynthesisError::Unsatisfiable);
        }
        Ok(())
    }

    fn right_shift<CS>(
        cs: &mut CS,
        v: &Num<F>,
        start_digit: usize,
        end_digit: usize,
    ) -> Result<Num<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let v_value = v.get_value().unwrap();
        let mut v_bits = v_value
            .to_le_bits()
            .into_iter()
            .skip(start_digit)
            .collect::<Vec<_>>();
        v_bits.truncate(end_digit - start_digit);
        
        let mut v_booleans: Vec<Boolean> = vec![];
        for (i, b) in v_bits.into_iter().enumerate() {
            let alloc_bit = AllocatedBit::alloc(
                cs.namespace(|| format!("allocate bit {i}")),
                Some(b),
            )?;
            v_booleans.push(Boolean::from(alloc_bit));
        }

        let mut sum_higher_order_bits = Num::<F>::zero();
        let mut sum_shifted_bits = Num::<F>::zero();
        let mut coeff= bigint_to_scalar::<F>(BigInt::from(1) << start_digit);
        let mut coeff_shifted  = F::one();

        for b in v_booleans {
            sum_higher_order_bits = sum_higher_order_bits.add_bool_with_coeff(CS::one(), &b, coeff);
            sum_shifted_bits = sum_shifted_bits.add_bool_with_coeff(CS::one(), &b, coeff_shifted);
            coeff_shifted = coeff_shifted.double();
            coeff = coeff.double();
        }

        cs.enforce(
            || "enforce equality between input value and weighted sum of higher order bits",
            |lc| lc,
            |lc| lc,
            |lc| lc + &v.lc(F::one()) - &sum_higher_order_bits.lc(F::one()),
        );
        
        Ok(sum_shifted_bits)
    }
    
    /// Asserts that the limbs represent the same integer value.
    /// For constant inputs, it ensures that the values are equal modulo the field order.
    /// For allocated inputs, it does not ensure that the values are equal modulo the field order.
    fn assert_limbs_equality<CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        a.enforce_width_conditional(&mut cs.namespace(|| "ensure bitwidths in a"))?;
        b.enforce_width_conditional(&mut cs.namespace(|| "ensure bitwidths in b"))?;

        if a.is_constant() && b.is_constant() {
            let a_i = BigInt::from(a);
            let b_i = BigInt::from(b);
            let a_r = a_i.rem(P::modulus());
            let b_r = b_i.rem(P::modulus());
            if a_r != b_r {
                eprintln!("Constant values are not equal");
                return Err(SynthesisError::Unsatisfiable);
            }
        }
        let (a_c, b_c, bits_per_limb) = Self::compact(a, b)?;

        if a.overflow > b.overflow {
            Self::assert_limbs_equality_slow(
                &mut cs.namespace(|| "check limbs equality"),
                &a_c,
                &b_c,
                bits_per_limb,
                a.overflow,
            )?;
        } else {
            Self::assert_limbs_equality_slow(
                &mut cs.namespace(|| "check limbs equality"),
                &b_c,
                &a_c,
                bits_per_limb,
                b.overflow,
            )?;
        }

        Ok(())
    }

    /// Asserts that the limbs represent the same integer value modulo the modulus.
    fn assert_is_equal<CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if a.is_constant() && b.is_constant() {
            let a_i = BigInt::from(a);
            let b_i = BigInt::from(b);
            let a_r = a_i.rem(P::modulus());
            let b_r = b_i.rem(P::modulus());
            if a_r != b_r {
                eprintln!("Constant values are not equal");
                return Err(SynthesisError::Unsatisfiable);
            }
        }

        let diff = a.sub(&mut cs.namespace(|| "a-b"), b)?;
        let k = diff.compute_quotient(&mut cs.namespace(|| "quotient when divided by modulus"))?;

        let kp = Self::reduce_and_apply_op(
            &mut cs.namespace(|| "computing product of quotient and modulus"),
            Optype::Mul,
            &k,
            &Self::modulus(),
        )?;

        Self::assert_limbs_equality(cs, &diff, &kp)?;

        Ok(())
    }

    pub fn reduce<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        self.enforce_width_conditional(&mut cs.namespace(|| "ensure bitwidths in input"))?;
        if self.overflow == 0 {
            return Ok(self.clone());
        }

        if self.is_constant() {
            eprintln!("Trying to reduce a constant with overflow flag set; should not happen");
            return Err(SynthesisError::Unsatisfiable);
        }

        let r = self.compute_rem(&mut cs.namespace(|| "remainder modulo field modulus"))?;
        Self::assert_is_equal(&mut cs.namespace(|| "check equality"), &r, self)?;
        Ok(r)
    }

    fn add_precondition(
        a: &Self,
        b: &Self,
    ) -> Result<usize, OverflowError> {
        let reduce_right = a.overflow < b.overflow;
        let next_overflow = a.overflow.max(b.overflow) + 1;

        if next_overflow > Self::max_overflow() {
            Err(OverflowError { op: Optype::Add, next_overflow, reduce_right })
        } else {
            Ok(next_overflow)
        }
    }

    fn add_op<CS>(
        a: &Self,
        b: &Self,
        next_overflow: usize,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if a.is_constant() && b.is_constant() {
            let a_int = BigInt::from(a);
            let b_int = BigInt::from(b);
            let res_int = (a_int + b_int).rem(P::modulus());
            return Ok(Self::from(&res_int));
        }

        let num_res_limbs = a.len().max(b.len());
        let mut res_lc: Vec<LinearCombination<F>> = vec![LinearCombination::<F>::zero(); num_res_limbs];
        let mut res_values: Vec<F> = vec![F::zero(); num_res_limbs];

        match (a.limbs.clone(), b.limbs.clone()) {
            (EmulatedLimbs::Constant(const_limbs), EmulatedLimbs::Allocated(var_limbs)) |
            (EmulatedLimbs::Allocated(var_limbs), EmulatedLimbs::Constant(const_limbs)) => {
                let var_limb_values = var_limbs.limb_values.clone().unwrap();
                for i in 0..num_res_limbs {
                    if i < var_limbs.limbs.len() {
                        res_lc[i] = res_lc[i].clone() + &var_limbs.limbs[i];
                        res_values[i] = res_values[i] + var_limb_values[i];
                    }
                    if i < const_limbs.len() {
                        res_lc[i] = res_lc[i].clone() + &LinearCombination::from_coeff(CS::one(), const_limbs[i]);
                        res_values[i] = res_values[i] + const_limbs[i];
                    }
                }
            },
            (EmulatedLimbs::Allocated(a_var), EmulatedLimbs::Allocated(b_var)) => {
                let a_var_limb_values = a_var.limb_values.clone().unwrap();
                let b_var_limb_values = b_var.limb_values.clone().unwrap();
                for i in 0..num_res_limbs {
                    if i < a_var.limbs.len() {
                        res_lc[i] = res_lc[i].clone() + &a_var.limbs[i];
                        res_values[i] = res_values[i] + a_var_limb_values[i];
                    }
                    if i < b_var.limbs.len() {
                        res_lc[i] = res_lc[i].clone() + &b_var.limbs[i];
                        res_values[i] = res_values[i] + b_var_limb_values[i];
                    }
                }
            },
            (EmulatedLimbs::Constant(_), EmulatedLimbs::Constant(_)) => panic!("Constant limb case has already been handled"),
        }

        let res = AllocatedLimbs::<F> {
            limbs: res_lc,
            limb_values: Some(res_values),
        };
        
        Ok(Self::new_internal_element(EmulatedLimbs::Allocated(res), next_overflow))
    }
    
    pub fn add<CS>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Self::reduce_and_apply_op(
            &mut cs.namespace(|| "compute a + b"),
            Optype::Add,
            self,
            other,
        )
    }

    fn sub_precondition(
        a: &Self,
        b: &Self,
    ) -> Result<usize, OverflowError> {
        let reduce_right = a.overflow < b.overflow;
        let next_overflow = a.overflow.max(b.overflow + 2);

        if next_overflow > Self::max_overflow() {
            Err(OverflowError { op: Optype::Sub, next_overflow, reduce_right })
        } else {
            Ok(next_overflow)
        }
    }

    /// Returns a k*P::modulus() for some k as a [EmulatedFieldElement]
    /// 
    /// Underflow may occur when computing a - b. Let d = [d[0], d[1], ...] be the padding.
    /// If d is a multiple of P::modulus() that is greater than b, then
    /// (a[0]+d[0]-b[0], a[1]+d[1]-b[1],...) will not underflow
    fn sub_padding(
        overflow: usize,
        limb_count: usize,
    ) -> Result<Vec<F>, SynthesisError> {
        let tmp = BigInt::from(1) << overflow + P::bits_per_limb();
        let upper_bound_limbs = vec![tmp; limb_count];

        let p = P::modulus();
        let mut padding_int_delta = recompose(&upper_bound_limbs, P::bits_per_limb())?;
        padding_int_delta = padding_int_delta.rem(&p);
        padding_int_delta = p - padding_int_delta;

        let padding_delta = decompose(&padding_int_delta, P::bits_per_limb(), limb_count)?;

        let padding_limbs = upper_bound_limbs
            .into_iter()
            .zip(padding_delta.into_iter())
            .map( |(a,b)| bigint_to_scalar(a+b))
            .collect::<Vec<F>>();
        
        Ok(padding_limbs)
    }

    fn sub_op<CS>(
        a: &Self,
        b: &Self,
        next_overflow: usize,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if a.is_constant() && b.is_constant() {
            let a_int = BigInt::from(a);
            let b_int = BigInt::from(b);
            let res_int = (a_int + b_int).rem(P::modulus());
            return Ok(Self::from(&res_int));
        }

        let num_res_limbs = a.len().max(b.len());
        let mut res_lc: Vec<LinearCombination<F>> = vec![LinearCombination::<F>::zero(); num_res_limbs];
        let mut res_values: Vec<F> = vec![F::zero(); num_res_limbs];
        let pad_limbs = Self::sub_padding(b.overflow, num_res_limbs)?;

        match (a.limbs.clone(), b.limbs.clone()) {
            (EmulatedLimbs::Allocated(a_var), EmulatedLimbs::Constant(b_const)) => {
                let a_var_limb_values = a_var.limb_values.clone().unwrap();
                for i in 0..num_res_limbs {
                    res_lc[i] = LinearCombination::from_coeff(CS::one(), pad_limbs[i]);
                    if i < a_var.limbs.len() {
                        res_lc[i] = res_lc[i].clone() + &a_var.limbs[i];
                        res_values[i] = res_values[i] + a_var_limb_values[i];
                    }
                    if i < b_const.len() {
                        res_lc[i] = res_lc[i].clone() - &LinearCombination::from_coeff(CS::one(), b_const[i]);
                        res_values[i] = res_values[i] - b_const[i];
                    }
                }
            },
            (EmulatedLimbs::Constant(a_const), EmulatedLimbs::Allocated(b_var)) => {
                let b_var_limb_values = b_var.limb_values.clone().unwrap();
                for i in 0..num_res_limbs {
                    res_lc[i] = LinearCombination::from_coeff(CS::one(), pad_limbs[i]);
                    if i < a_const.len() {
                        res_lc[i] = res_lc[i].clone() + &LinearCombination::from_coeff(CS::one(), a_const[i]);
                        res_values[i] = res_values[i] + a_const[i];
                    }
                    if i < b_var.limbs.len() {
                        res_lc[i] = res_lc[i].clone() - &b_var.limbs[i];
                        res_values[i] = res_values[i] - b_var_limb_values[i];
                    }
                }
            },
            (EmulatedLimbs::Allocated(a_var), EmulatedLimbs::Allocated(b_var)) => {
                let a_var_limb_values = a_var.limb_values.clone().unwrap();
                let b_var_limb_values = b_var.limb_values.clone().unwrap();
                for i in 0..num_res_limbs {
                    res_lc[i] = LinearCombination::from_coeff(CS::one(), pad_limbs[i]);
                    if i < a_var.limbs.len() {
                        res_lc[i] = res_lc[i].clone() + &a_var.limbs[i];
                        res_values[i] = res_values[i] + a_var_limb_values[i];
                    }
                    if i < b_var.limbs.len() {
                        res_lc[i] = res_lc[i].clone() - &b_var.limbs[i];
                        res_values[i] = res_values[i] - b_var_limb_values[i];
                    }
                }
            },
            (EmulatedLimbs::Constant(_), EmulatedLimbs::Constant(_)) => panic!("Constant limb case has already been handled"),
        }

        let res = AllocatedLimbs::<F> {
            limbs: res_lc,
            limb_values: Some(res_values),
        };
        
        Ok(Self::new_internal_element(EmulatedLimbs::Allocated(res), next_overflow))
    }

    pub fn sub<CS>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Self::reduce_and_apply_op(
            &mut cs.namespace(|| "compute a - b"),
            Optype::Sub,
            self,
            other,
        )
    }

    pub fn neg<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let zero = Self::zero();
        zero.sub(&mut cs.namespace(|| "negate"), self)
    }

    fn mul_precondition(
        a: &Self,
        b: &Self,
    ) -> Result<usize, OverflowError> {
        let reduce_right = a.overflow < b.overflow;
        let max_carry_bits = (a.len().min(b.len()) as f32).log2().ceil() as usize;
        let next_overflow = P::bits_per_limb() + a.overflow + b.overflow + max_carry_bits;

        if next_overflow > Self::max_overflow() {
            Err(OverflowError { op: Optype::Mul, next_overflow, reduce_right })
        } else {
            Ok(next_overflow)
        }
    }

    fn mul_op<CS>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        next_overflow: usize,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if a.is_constant() && b.is_constant() {
            let a_int = BigInt::from(a);
            let b_int = BigInt::from(b);
            let res_int = (a_int * b_int).rem(P::modulus());
            return Ok(Self::from(&res_int));
        }

        let num_prod_limbs = a.len() + b.len() - 1;
        let mut prod_lc: Vec<LinearCombination<F>> = vec![LinearCombination::<F>::zero(); num_prod_limbs];
        let mut prod_values: Vec<F> = vec![F::zero(); num_prod_limbs];

        match (a.limbs.clone(), b.limbs.clone()) {
            (EmulatedLimbs::Constant(const_limbs), EmulatedLimbs::Allocated(var_limbs)) |
            (EmulatedLimbs::Allocated(var_limbs), EmulatedLimbs::Constant(const_limbs)) => {
                let var_limb_values = var_limbs.limb_values.clone().unwrap();
                for i in 0..var_limbs.limbs.len() {
                    for j in 0..const_limbs.len() {
                        prod_lc[i+j] = prod_lc[i+j].clone() + &mul_lc_with_scalar(&var_limbs.limbs[i], &const_limbs[i]);
                        prod_values[i+j] = prod_values[i+j] + var_limb_values[i] * const_limbs[i];
                    }
                }
            },
            (EmulatedLimbs::Allocated(a_var), EmulatedLimbs::Allocated(b_var)) => {
                let a_var_limb_values = a_var.limb_values.clone().unwrap();
                let b_var_limb_values = b_var.limb_values.clone().unwrap();
                for i in 0..a.len() {
                    for j in 0..b.len() {
                        prod_values[i+j] += a_var_limb_values[i] * b_var_limb_values[i];
                    }
                }

                prod_lc = (0..num_prod_limbs)
                    .map(|i| {
                        cs.alloc(
                            || format!("product limb {i}"),
                            || Ok(prod_values[i]),
                        )
                        .map(|v| LinearCombination::<F>::zero() + v)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let mut c = F::zero();
                for _ in 0..num_prod_limbs {
                    c += F::one();
                    cs.enforce(
                        || format!("pointwise product @ {c:?}"),
                        |lc| {
                            let mut coeff = F::one();
                            a_var.limbs.iter().fold(lc, |acc, elem| {
                                let r = acc + (coeff, elem);
                                coeff *= c;
                                r
                            })
                        },
                        |lc| {
                            let mut coeff = F::one();
                            b_var.limbs.iter().fold(lc, |acc, elem| {
                                let r = acc + (coeff, elem);
                                coeff *= c;
                                r
                            })
                        },
                        |lc| {
                            let mut coeff = F::one();
                            prod_lc.iter().fold(lc, |acc, elem| {
                                let r = acc + (coeff, elem);
                                coeff *= c;
                                r
                            })
                        },
                    )
                }
            },
            (EmulatedLimbs::Constant(_), EmulatedLimbs::Constant(_)) => panic!("Constant limb case has already been handled"),
        }

        let res = AllocatedLimbs::<F> {
            limbs: prod_lc,
            limb_values: Some(prod_values),
        };
        
        Ok(Self::new_internal_element(EmulatedLimbs::Allocated(res), next_overflow))
    }

    pub fn mul<CS>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        Self::reduce_and_apply_op(
            &mut cs.namespace(|| "compute a * b"),
            Optype::Mul,
            self,
            other,
        )
    }

    pub fn inverse<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let a_inv = self.compute_inverse(&mut cs.namespace(|| "multiplicative inverse"))?;
        let prod = self.mul(
            &mut cs.namespace(|| "product of a and a_inv"),
            &a_inv
        )?;
        Self::assert_is_equal(
            &mut cs.namespace(|| "product equals one"),
            &prod,
            &Self::one(),
        )?;
        
        Ok(a_inv)
    }

    pub fn divide<CS>(
        &self,
        cs: &mut CS,
        denom: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let ratio = self.compute_ratio(
            &mut cs.namespace(|| "ratio"),
            denom
        )?;
        let prod = ratio.mul(
            &mut cs.namespace(|| "product of ratio and denominator"),
            &denom,
        )?;
        Self::assert_is_equal(
            &mut cs.namespace(|| "product equals numerator"),
            &prod,
            self,
        )?;

        Ok(ratio)
    }

    fn reduce_and_apply_op<CS>(
        cs: &mut CS,
        op_type: Optype,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        a.enforce_width_conditional(&mut cs.namespace(|| "ensure bitwidths in a"))?;
        b.enforce_width_conditional(&mut cs.namespace(|| "ensure bitwidths in b"))?;

        let precondition = match op_type {
            Optype::Add => Self::add_precondition,
            Optype::Sub => Self::sub_precondition,
            Optype::Mul => Self::mul_precondition,
        };

        let mut a_r: Self = a.clone();
        let mut b_r: Self = b.clone();
        let next_overflow: usize = loop {
            let res =  precondition(a, b);
            if res.is_ok() {
                let res_next_overflow = res.unwrap();                
                break res_next_overflow;
            }
            else {
                let err = res.err().unwrap();
                if err.reduce_right {
                    a_r = a_r.reduce(
                        &mut cs.namespace(|| "reduce a" ),
                    )?;
                }
                else {
                    b_r = b_r.reduce(
                        &mut cs.namespace(|| "reduce b" ),
                    )?;
                }
            }
        };

        let res = match op_type {
            Optype::Add => Self::add_op::<CS>(&a_r, &b_r, next_overflow),
            Optype::Sub => Self::sub_op::<CS>(&a_r,&b_r, next_overflow),
            Optype::Mul => Self::mul_op(&mut cs.namespace(|| "mul_op"), &a_r,&b_r, next_overflow),
        };

        res
    }


}
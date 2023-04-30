use std::ops::Rem;

use bellperson::{LinearCombination, SynthesisError, ConstraintSystem, Variable, gadgets::boolean::Boolean};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::{BigInt, Sign};

/// Multiply a LinearCombination by a scalar
pub fn mul_lc_with_scalar<F>(
    lc: &LinearCombination<F>,
    scalar: &F
) -> LinearCombination<F>
where
    F: PrimeField
{
    let mut scaled_lc = LinearCombination::<F>::zero();
    for (var, coeff) in lc.iter() {
        scaled_lc = scaled_lc + (*scalar*coeff, var);
    }
    scaled_lc
}

/// Range check an expression represented by a LinearCombination
///
/// From `fits_in_bits` of `bellperson-nonnative`
pub fn range_check_lc<F, CS>(
    cs: &mut CS,
    lc_input: &LinearCombination<F>,
    lc_value: F,
    num_bits: usize,
) -> Result<(), SynthesisError>
where
    F: PrimeField + PrimeFieldBits,
    CS: ConstraintSystem<F>,
{
    let value_bits = lc_value.to_le_bits();

    // Allocate all but the first bit.
    let bits: Vec<Variable> = (1..num_bits)
        .map(|i| {
            cs.alloc(
                || format!("bit {i}"),
                || {
                    let r = if value_bits[i] {
                        F::one()
                    } else {
                        F::zero()
                    };
                    Ok(r)
                },
            )
        })
        .collect::<Result<_, _>>()?;

    for (i, v) in bits.iter().enumerate() {
        cs.enforce(
            || format!("bit {i} is bit"),
            |lc| lc + *v,
            |lc| lc + CS::one() - *v,
            |lc| lc,
        )
    }

    // Last bit
    cs.enforce(
        || format!("last bit of variable is a bit"),
        |mut lc| {
            let mut f = F::one();
            lc = lc + lc_input;
            for v in bits.iter() {
                f = f.double();
                lc = lc - (f, *v);
            }
            lc
        },
        |mut lc| {
            lc = lc + CS::one();
            let mut f = F::one();
            lc = lc - lc_input;
            for v in bits.iter() {
                f = f.double();
                lc = lc + (f, *v);
            }
            lc
        },
        |lc| lc,
    );

    Ok(())
}

/// Range check a constant field element
pub fn range_check_constant<F>(
    value: F,
    num_bits: usize,
) -> Result<(), SynthesisError>
where
    F: PrimeField + PrimeFieldBits,
{
    let value_bits = value.to_le_bits();
    let mut res = F::zero();
    let mut coeff = F::one();
    for i in 0..num_bits {
        if value_bits[i] {
            res += coeff;
        }
        coeff = coeff.double();
    }
    if res != value {
        eprintln!("value does not fit in the required number of bits");
        return Err(SynthesisError::Unsatisfiable);
    }

    Ok(())
}

/// Convert a non-negative BigInt into a field element
pub fn bigint_to_scalar<F>(
    value: BigInt,
) -> F
where
    F: PrimeField + PrimeFieldBits,
{
    assert!(value.bits() as u32 <= F::CAPACITY);
    let (s, v) = value.into_parts();
    assert_ne!(s, Sign::Minus);

    let mut base = F::from(u64::MAX);
    base = base + F::one(); // 2^64 in the field
    let mut coeff = F::one();
    let mut res = F::zero();

    for d in v.to_u64_digits().into_iter() {
        let d_f = F::from(d);
        res += d_f * coeff;
        coeff = coeff*base;
    }
    res
}

/// Construct a [BigInt] from a vector of [BigInt] limbs with base equal to 2^num_bits_per_limb
pub fn recompose(
    limbs: &Vec<BigInt>,
    num_bits_per_limb: usize,
) -> Result<BigInt, SynthesisError> {
    if limbs.len() == 0{
        eprintln!("Empty input");
        return Err(SynthesisError::Unsatisfiable);
    }
    
    let mut res = BigInt::from(0);
    for i in 0..limbs.len() {
        res <<= num_bits_per_limb;
        res += &limbs[limbs.len()-i-1];
    }
    Ok(res)
}

/// Decompose a [BigInt] into a vector of [BigInt] limbs each occupying `num_bits_per_limb` bits.
pub fn decompose(
    input: &BigInt,
    num_bits_per_limb: usize,
    num_limbs: usize,
) -> Result<Vec<BigInt>, SynthesisError> {
    if input.bits() as usize > num_limbs * num_bits_per_limb {
        eprintln!("Not enough limbs to represent input {:?}", input);
        return Err(SynthesisError::Unsatisfiable);
    }

    let mut res = vec![BigInt::from(0); num_limbs];
    let base = BigInt::from(1) << num_bits_per_limb;
    let mut tmp = input.clone();
    for i in 0..num_limbs {
        res[i] = tmp.clone().rem(&base);
        tmp >>= num_bits_per_limb;
    }
    Ok(res)
}

/// Copy of bellman::gadgets::num to access the otherwise private fields.
pub struct Num<F: PrimeField> {
    pub lc: LinearCombination<F>,
    pub value: Option<F>,
}


impl<F: PrimeField> Num<F> {
    pub fn new(value: Option<F>, num: LinearCombination<F>) -> Self {
        Self { value, lc: num }
    }

    pub fn zero() -> Self {
        Num {
            value: Some(F::zero()),
            lc: LinearCombination::zero(),
        }
    }

    pub fn get_value(&self) -> Option<F> {
        self.value
    }

    pub fn lc(&self, coeff: F) -> LinearCombination<F> {
        LinearCombination::zero() + (coeff, &self.lc)
    }

    pub fn add_bool_with_coeff(self, one: Variable, bit: &Boolean, coeff: F) -> Self {
        let newval = match (self.value, bit.get_value()) {
            (Some(mut curval), Some(bval)) => {
                if bval {
                    curval.add_assign(&coeff);
                }

                Some(curval)
            }
            _ => None,
        };

        Num {
            value: newval,
            lc: self.lc + &bit.lc(one, coeff),
        }
    }

    pub fn add(self, other: &Self) -> Self {
        let lc = self.lc + &other.lc;
        let value = match (self.value, other.value) {
            (Some(v1), Some(v2)) => {
                let mut tmp = v1;
                tmp.add_assign(&v2);
                Some(tmp)
            }
            (Some(v), None) | (None, Some(v)) => Some(v),
            (None, None) => None,
        };

        Num { value, lc }
    }

    pub fn scale(mut self, scalar: F) -> Self {
        for (_variable, fr) in self.lc.iter_mut() {
            fr.mul_assign(&scalar);
        }

        if let Some(ref mut v) = self.value {
            v.mul_assign(&scalar);
        }

        self
    }
}
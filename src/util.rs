use bellperson::{LinearCombination, SynthesisError, ConstraintSystem, Variable};
use ff::{PrimeField, PrimeFieldBits};

/// Multiply a LinearCombination by a scalar
pub fn mul_lc_with_scalar<F>(
    lc: LinearCombination<F>,
    scalar: F
) -> LinearCombination<F>
where
    F: PrimeField
{
    let mut scaled_lc = LinearCombination::<F>::zero();
    for (var, coeff) in lc.iter() {
        scaled_lc = scaled_lc + (scalar*coeff, var);
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
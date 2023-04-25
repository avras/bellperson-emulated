use ff::{PrimeField, PrimeFieldBits};
use num_bigint::BigInt;

use crate::{element::EmulatedFieldElement, params::EmulatedFieldParams};

pub struct EmulatedField<F: PrimeField + PrimeFieldBits, P: EmulatedFieldParams> {
    zero: EmulatedFieldElement<F, P>,
    one: EmulatedFieldElement<F, P>,
    modulus: EmulatedFieldElement<F, P>,
    max_overflow: usize,
}

impl<F, P> EmulatedField<F, P>
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams,
{
    pub fn new() -> Self {
        let zero = EmulatedFieldElement::<F, P>::from(&BigInt::from(0));
        let one = EmulatedFieldElement::<F, P>::from(&BigInt::from(1));
        let modulus = EmulatedFieldElement::<F, P>::from(&P::modulus());
        let max_overflow = (F::NUM_BITS as usize) - 1 - P::bits_per_limb();

        Self { zero, one, modulus, max_overflow }
    }
}
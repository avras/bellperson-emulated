use num_bigint::{BigInt, Sign};

/// Emulated field is assumed to be prime. So inverses alway
/// exist for non-zero field elements
pub trait EmulatedFieldParams {
    fn num_limbs() -> usize;
    fn bits_per_limb() -> usize;
    fn modulus() -> BigInt;
}


/// Ed25519 base field parameters
pub struct Ed25519Fp;

impl EmulatedFieldParams for Ed25519Fp {
    fn num_limbs() -> usize {
        5
    }

    fn bits_per_limb() -> usize {
        51
    }

    fn modulus() -> BigInt {
        BigInt::from_bytes_be(Sign::Plus, b"7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed")
    }
}

/// Ed25519 scalar field parameters
pub struct Ed25519Fr;

impl EmulatedFieldParams for Ed25519Fr {
    fn num_limbs() -> usize {
        5
    }

    fn bits_per_limb() -> usize {
        51
    }

    fn modulus() -> BigInt {
        BigInt::from_bytes_be(Sign::Plus, b"1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed")
    }
}
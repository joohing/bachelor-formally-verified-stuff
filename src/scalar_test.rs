#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;
    use crate::*;

    #[quickcheck]
    /// Assert that each element has a multiplicative inverse.
    fn field_multiplicative_inverse(n: u128) -> bool {
        let n = Scalar::from(n);
        let n = if n == Scalar::ZERO { Scalar::from(1u128) } else { n };
        n * n.invert() == Scalar::from(1u128)
    }

    #[quickcheck]
    /// Assert multiplication is correct
    fn field_multiplication_correct(a: u128, b: u128) -> bool {
        let exp = (a % PRIME) * (b % PRIME) % PRIME;
        let res = Scalar::from(a) * Scalar::from(b);
        Scalar { v: exp } == res
    }

    #[quickcheck]
    /// Assert that each element inverted twice results in the original.
    fn field_double_invert(n: u128) -> bool {
        Scalar::from(n).invert().invert() == Scalar::from(n)
    }

    #[quickcheck]
    /// Assert that each element plus its additive inverse equals zero.
    fn field_additive_inverse(n: u128) -> bool {
        let scalar = Scalar::from(n);
        scalar + (Scalar::ZERO - scalar) == Scalar::ZERO
    }

    #[quickcheck]
    /// Assert that inversion works properly for powers.
    fn field_power_inverse(n: u128, x: u16) -> bool {
        Scalar::from(n).pow(x as u128).invert() == Scalar::from(n).invert().pow(x as u128)
    }

    #[quickcheck]
    fn field_distributive_law(x: u64, y: u64, z: u64) -> bool {
        let sx = Scalar::from(x as u128);
        let sy = Scalar::from(y as u128);
        let sz = Scalar::from(z as u128);
        (sx + sy) * sz == sx * sz + sy * sz
    }

    #[test]
    fn field_one_multiplicative_inverse() {
        let one = Scalar::from(1u128);
        println!("one invrted: {}", one.invert());
        assert!(one * one.invert() == Scalar::from(1u128));
    }

    #[test]
    fn field_basic_arithmetic() {
        let one = Scalar::from(1u128);
        assert!(one + one == Scalar::from(2u128));
    }
}

use num_bigint::{ BigInt, BigUint, Sign };
use std::num::Wrapping;
use crate::bigint;

pub fn calc_nsafe(log_limb_size: u32) -> usize {
    let max_int_width = 32;
    let rhs = 2u64.pow(max_int_width);
    let mut k = 1usize;
    let x = 2u64.pow(2u32 * log_limb_size);
    while (k as u64) * x <= rhs {
        k += 1;
    }

    k / 2
}

pub fn calc_mont_radix(
    num_limbs: usize,
    log_limb_size: u32
) -> BigUint {
    BigUint::from(2u32).pow(num_limbs as u32 * log_limb_size)
}

fn egcd(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
    if *a == BigInt::from(0u32) {
        return (b.clone(), BigInt::from(0u32), BigInt::from(1u32));
    }
    let (g, x, y) = egcd(&(b % a), a);

    (g, y - (b / a) * x.clone(), x.clone())
}

pub fn calc_inv_and_pprime(
    p: &BigUint,
    r: &BigUint,
) -> (BigUint, BigUint) {
    assert!(*r != BigUint::from(0u32));

    let p_bigint = BigInt::from_biguint(Sign::Plus, p.clone());
    let r_bigint = BigInt::from_biguint(Sign::Plus, r.clone());
    let one = BigInt::from(1u32);
    let (_, mut rinv, mut pprime) = egcd(
        &BigInt::from_biguint(Sign::Plus, r.clone()),
        &BigInt::from_biguint(Sign::Plus, p.clone())
    );

    if rinv.sign() == Sign::Minus {
        rinv = BigInt::from_biguint(Sign::Plus, p.clone()) + rinv;
    }

    if pprime.sign() == Sign::Minus {
        pprime = BigInt::from_biguint(Sign::Plus, r.clone()) + pprime;
    }

    // r * rinv - p * pprime == 1
    assert!(
        (BigInt::from_biguint(Sign::Plus, r.clone()) * &rinv % &p_bigint) -
            (&p_bigint * &pprime % &p_bigint)
        == one
    );

    // r * rinv % p == 1
    assert!((BigInt::from_biguint(Sign::Plus, r.clone()) * &rinv % &p_bigint) == one);

    // p * pprime % r == 1
    assert!(
        (&p_bigint * &pprime % &r_bigint) == one
    );

    (
        rinv.to_biguint().unwrap(),
        pprime.to_biguint().unwrap(),
    )
}

pub fn calc_rinv_and_n0(
    p: &BigUint,
    r: &BigUint,
    log_limb_size: u32
) -> (BigUint, u32) {
    let (rinv, pprime) = calc_inv_and_pprime(p, r);
    let pprime = BigInt::from_biguint(Sign::Plus, pprime);

    let neg_n_inv = BigInt::from_biguint(Sign::Plus, r.clone()) - pprime;
    let n0 = neg_n_inv % BigInt::from(2u32.pow(log_limb_size as u32));
    let n0 = n0.to_biguint().unwrap().to_u32_digits()[0];

    (rinv, n0)
}

/// An optimised variant of the Montgomery product algorithm from
/// https://github.com/mitschabaude/montgomery#13-x-30-bit-multiplication.
pub fn mont_mul_optimised(
    x: &Vec<u32>,
    y: &Vec<u32>,
    p: &Vec<u32>,
    n0: u32,
    num_limbs: usize,
    log_limb_size: u32
) -> Vec<u32> {
    assert!(log_limb_size == 12 || log_limb_size == 13);
    assert!(x.len() == num_limbs);
    assert!(y.len() == num_limbs);
    assert!(p.len() == num_limbs);

    let mut s = vec![0u32; num_limbs];

    let mask = 2u32.pow(log_limb_size) - 1u32;

    for i in 0..num_limbs {
        let t = (Wrapping(s[0]) + Wrapping(x[i]) * Wrapping(y[0])).0;
        let tprime = t & mask;
        let qi = (n0 * tprime) & mask;
        let c = (Wrapping(t) + Wrapping(qi) * Wrapping(p[0])).0 >> log_limb_size;
        s[0] = (Wrapping(s[1]) + Wrapping(x[i]) * Wrapping(y[1]) + Wrapping(qi) * Wrapping(p[1]) + Wrapping(c)).0;

        for j in 2..num_limbs {
            s[j - 1] = (Wrapping(s[j]) + Wrapping(x[i]) * Wrapping(y[j]) + Wrapping(qi) * Wrapping(p[j])).0;
        }
        s[num_limbs - 2] = (Wrapping(x[i]) * Wrapping(y[num_limbs - 1]) + Wrapping(qi) * Wrapping(p[num_limbs - 1])).0;
    }

    let mut c = 0u32;
    for i in 0..num_limbs {
        let v = (Wrapping(s[i]) + Wrapping(c)).0;
        c = v >> log_limb_size;
        s[i] = v & mask;
    }

    conditional_reduce(&s, &p, log_limb_size)
}

/// An modified variant of the Montgomery product algorithm from
/// https://github.com/mitschabaude/montgomery#13-x-30-bit-multiplication.
pub fn mont_mul_modified(
    x: &Vec<u32>,
    y: &Vec<u32>,
    p: &Vec<u32>,
    n0: u32,
    num_limbs: usize,
    log_limb_size: u32,
    nsafe: usize
) -> Vec<u32> {
    assert!(log_limb_size == 14 || log_limb_size == 15);
    assert!(x.len() == num_limbs);
    assert!(y.len() == num_limbs);
    assert!(p.len() == num_limbs);

    let mut s = vec![0u32; num_limbs];

    let mask = 2u32.pow(log_limb_size) - 1u32;
    for i in 0..num_limbs {
        let t = (Wrapping(s[0]) + Wrapping(x[i]) * Wrapping(y[0])).0;
        let tprime = t & mask;
        let qi = (n0 * tprime) & mask;
        let mut c = (Wrapping(t) + Wrapping(qi) * Wrapping(p[0])).0 >> log_limb_size;

        for j in 1..num_limbs - 1 {
            let mut t = (Wrapping(s[j]) + Wrapping(x[i]) * Wrapping(y[j]) + Wrapping(qi) * Wrapping(p[j])).0;
            if (j - 1) % nsafe == 0 {
                t = (Wrapping(t) + Wrapping(c)).0;
            }

            c = t >> log_limb_size;

            if j % nsafe == 0 {
                c = t >> log_limb_size;
                s[j - 1] = t & mask;
            } else {
                s[j - 1] = t;
            }
        }
        s[num_limbs - 2] = (Wrapping(x[i]) * Wrapping(y[num_limbs - 1]) + Wrapping(qi) * Wrapping(p[num_limbs - 1])).0;

        // The following follows mitschabaude's algo more closely, while the above skips some
        // unnecessary steps given certain parameters
        /*
        for j in 1..num_limbs - 1 {
            let mut t = (Wrapping(s[j]) + Wrapping(x[i]) * Wrapping(y[j]) + Wrapping(qi) * Wrapping(p[j])).0;
            if (j - 1) % nsafe == 0 {
                t = (Wrapping(t) + Wrapping(c)).0;
            }

            if j % nsafe == 0 {
                c = t >> log_limb_size;
                s[j - 1] = t & mask;
            } else {
                s[j - 1] = t;
            }
        }

        if num_limbs - 2 % nsafe == 0 {
            let r = (Wrapping(s[num_limbs - 1]) + Wrapping(x[i]) * Wrapping(y[num_limbs - 1]) + Wrapping(qi) * Wrapping(p[num_limbs - 1])).0;
            s[num_limbs - 2] = r & mask;
            c = r >> log_limb_size;
            s[num_limbs - 1] = c;
        } else {
            s[num_limbs - 2] = (Wrapping(x[i]) * Wrapping(y[num_limbs - 1]) + Wrapping(qi) * Wrapping(p[num_limbs - 1])).0;
        }
        */
    }

    let mut c = 0u32;
    for i in 0..num_limbs {
        let v = (Wrapping(s[i]) + Wrapping(c)).0;
        c = v >> log_limb_size;
        s[i] = v & mask;
    }

    conditional_reduce(&s, &p, log_limb_size)
}

fn conditional_reduce(x: &Vec<u32>, y: &Vec<u32>, log_limb_size: u32) -> Vec<u32> {
    if bigint::gte(x, y) {
        return bigint::sub(x, y, log_limb_size);
    }

    x.clone()
}

#[cfg(test)]
pub mod tests {
    use rand::Rng;
    use rand_chacha::ChaCha8Rng;
    use rand_chacha::rand_core::SeedableRng;

    use crate::bigint;
    use crate::utils::{
        calc_num_limbs,
        calc_bitwidth,
    };
    use crate::mont::{
        calc_mont_radix,
        calc_rinv_and_n0,
        calc_nsafe,
        mont_mul_optimised,
        mont_mul_modified
    };
    use num_bigint::{ BigUint, RandomBits };

    #[test]
    pub fn test_calc_num_limbs() {
        assert!(calc_num_limbs(13, 254) == 20);
        assert!(calc_num_limbs(13, 377) == 30);
    }

    #[test]
    pub fn test_calc_bitwidth() {
        let p = BigUint::parse_bytes(b"00", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);
        assert!(p_bitwidth == 0);

        let p = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);
        assert!(p_bitwidth == 256);

        let p = BigUint::parse_bytes(b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);
        assert!(p_bitwidth == 253);
    }

    #[test]
    pub fn test_calc_rinv_and_n0() {
        // Use the BLS12-377 scalar field as a known example
        let p = BigUint::parse_bytes(b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
        let num_limbs = 20;
        let log_limb_size = 13;
        let r = calc_mont_radix(num_limbs, log_limb_size);
        let res = calc_rinv_and_n0(&p, &r, log_limb_size);
        let rinv = res.0;
        let n0 = res.1;

        assert!(rinv == BigUint::parse_bytes(b"10d128cbd9101cae5cd618f8b32be2e42a4713084d4fee883ce17dd1a1beeec1", 16).unwrap());
        assert!(n0 == 8191u32);
    }

    fn mont_mul_optimised_test(
        a: &BigUint,
        b: &BigUint,
        p: &BigUint,
        num_limbs: usize,
        log_limb_size: u32
    ) {
        let r = calc_mont_radix(num_limbs, log_limb_size);
        let res = calc_rinv_and_n0(&p, &r, log_limb_size);
        let n0 = res.1;
        let p_limbs = bigint::from_biguint_le(&p, num_limbs, log_limb_size);
        let a_r = a * &r % p;
        let b_r = b * &r % p;
        let expected = a * b * &r % p;
        let expected_limbs = bigint::from_biguint_le(&expected, num_limbs, log_limb_size);

        let a_r_limbs = bigint::from_biguint_le(&a_r, num_limbs, log_limb_size);
        let b_r_limbs = bigint::from_biguint_le(&b_r, num_limbs, log_limb_size);
        let res = mont_mul_optimised(&a_r_limbs, &b_r_limbs, &p_limbs, n0, num_limbs, log_limb_size);

        assert!(bigint::eq(&res, &expected_limbs));
    }

    fn mont_mul_modified_test(
        a: &BigUint,
        b: &BigUint,
        p: &BigUint,
        num_limbs: usize,
        log_limb_size: u32
    ) {
        let nsafe = calc_nsafe(log_limb_size);
        let r = calc_mont_radix(num_limbs, log_limb_size);
        let res = calc_rinv_and_n0(&p, &r, log_limb_size);
        let n0 = res.1;

        let p_limbs = bigint::from_biguint_le(&p, num_limbs, log_limb_size);
        let a_r = a * &r % p;
        let b_r = b * &r % p;
        let expected = a * b * &r % p;
        let expected_limbs = bigint::from_biguint_le(&expected, num_limbs, log_limb_size);

        let a_r_limbs = bigint::from_biguint_le(&a_r, num_limbs, log_limb_size);
        let b_r_limbs = bigint::from_biguint_le(&b_r, num_limbs, log_limb_size);
        let res = mont_mul_modified(&a_r_limbs, &b_r_limbs, &p_limbs, n0, num_limbs, log_limb_size, nsafe);

        assert!(bigint::eq(&res, &expected_limbs));
    }

    #[test]
    pub fn test_bls12_377_mont_mul_optimised() {
        let p = BigUint::parse_bytes(b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);
        for log_limb_size in 12..14 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);

            let a = BigUint::parse_bytes(b"10ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
            let b = BigUint::parse_bytes(b"11ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();

            mont_mul_optimised_test(&a, &b, &p, num_limbs, log_limb_size);
        }
    }

    #[test]
    pub fn test_bls12_377_mont_mul_optimised_rand() {
        let p = BigUint::parse_bytes(b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);

        for log_limb_size in 12..14 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);
            for i in 0..100 {
                let mut rng = ChaCha8Rng::seed_from_u64(i as u64);
                let a: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                let b: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                mont_mul_optimised_test(&a, &b, &p, num_limbs, log_limb_size);
            }
        }
    }

    #[test]
    pub fn test_secp256k1_mont_mul_optimised() {
        let p = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);
        for log_limb_size in 12..13 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);

            let a = BigUint::parse_bytes(b"10ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
            let b = BigUint::parse_bytes(b"11ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();

            mont_mul_optimised_test(&a, &b, &p, num_limbs, log_limb_size);
        }
    }

    #[test]
    pub fn test_secp256k1_mont_mul_optimised_rand() {
        let p = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);

        for log_limb_size in 12..14 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);
            for i in 0..100 {
                let mut rng = ChaCha8Rng::seed_from_u64(i as u64);
                let a: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                let b: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                mont_mul_optimised_test(&a, &b, &p, num_limbs, log_limb_size);
            }
        }
    }

    #[test]
    pub fn test_bls12_377_mont_mul_modified() {
        let p = BigUint::parse_bytes(b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);
        for log_limb_size in 15..16 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);

            let a = BigUint::parse_bytes(b"10ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
            let b = BigUint::parse_bytes(b"11ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();

            mont_mul_modified_test(&a, &b, &p, num_limbs, log_limb_size);
        }
    }

    #[test]
    pub fn test_secp256k1_mont_mul_modified() {
        let p = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);
        for log_limb_size in 14..16 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);

            let a = BigUint::parse_bytes(b"10ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
            let b = BigUint::parse_bytes(b"11ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();

            mont_mul_modified_test(&a, &b, &p, num_limbs, log_limb_size);
        }
    }

    #[test]
    pub fn test_secp256k1_mont_mul_modified_rand() {
        let p = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);

        for log_limb_size in 14..16 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);
            for i in 0..100 {
                let mut rng = ChaCha8Rng::seed_from_u64(i as u64);
                let a: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                let b: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                mont_mul_modified_test(&a, &b, &p, num_limbs, log_limb_size);
                mont_mul_modified_test(&a, &b, &p, num_limbs, log_limb_size);
            }
        }
    }

    #[test]
    pub fn test_bls12_377_mont_mul_modified_rand() {
        let p = BigUint::parse_bytes(b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);

        for log_limb_size in 14..16 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);
            for i in 0..100 {
                let mut rng = ChaCha8Rng::seed_from_u64(i as u64);
                let a: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                let b: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                mont_mul_modified_test(&a, &b, &p, num_limbs, log_limb_size);
            }
        }
    }
}

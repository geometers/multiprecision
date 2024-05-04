use num_bigint::{ BigInt, BigUint, Sign };
use std::num::Wrapping;
use crate::{ bigint, ff };

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

    ff::reduce(&s, &p, log_limb_size)
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

    ff::reduce(&s, &p, log_limb_size)
}

/// Given xr, returns the modular square root(s) of x in Montgomery form. Assumes that the field modulus is p and p mod 4 == 3
/// In other words, returns sqrt(x)r given xr.
/// ±x^((p + 1) / 4) mod p
pub fn sqrt_case3mod4(
    xr_limbs: &Vec<u32>, 
    p_limbs: &Vec<u32>, 
    r_limbs: &Vec<u32>, 
    n0: u32,
    num_limbs: usize,
    log_limb_size: u32,
    nsafe: usize
) -> (Vec<u32>, Vec<u32>) {
    let mut one = vec![0u32; num_limbs];
    one[0] = 1u32;
    // exponent_limbs should be precomputed
    let p_plus_1 = bigint::add_unsafe(&p_limbs, &one, log_limb_size);
    let p_plus_1_div_2 = bigint::div2(&p_plus_1, log_limb_size);
    let exponent_limbs = bigint::div2(&p_plus_1_div_2, log_limb_size);
 
    let s = modpow(&xr_limbs, &r_limbs, &exponent_limbs, &p_limbs, n0, num_limbs, log_limb_size, nsafe);

    (s.clone(), ff::sub(&p_limbs, &s, &p_limbs, log_limb_size))
}

pub fn modpow(
    xr: &Vec<u32>,
    r: &Vec<u32>,
    exponent: &Vec<u32>,
    p: &Vec<u32>,
    n0: u32,
    num_limbs: usize,
    log_limb_size: u32,
    nsafe: usize
) -> Vec<u32> {
    /*
    let mut result = 1;
    let mut temp = x;
    let mut s = n;
    while s != 0 {
        if s % 2 == 1 {
            result *= temp;
        }
        temp = temp * temp;
        s = s >> 1;
    }
    result
    */
    fn mont_mul_func(
        x: &Vec<u32>,
        y: &Vec<u32>,
        p: &Vec<u32>,
        n0: u32,
        num_limbs: usize,
        log_limb_size: u32,
        nsafe: usize
    ) -> Vec<u32> {
        if log_limb_size > 10 && log_limb_size < 14 {
            mont_mul_optimised(x, y, p, n0, num_limbs, log_limb_size)
        } else {
            mont_mul_modified(x, y, p, n0, num_limbs, log_limb_size, nsafe)
        }
    }
    let mut result = r.clone();
    let mut temp = xr.clone();
    let mut s = exponent.clone();

    while !bigint::is_zero(&s) {
        if !bigint::is_even(&s) {
            result = mont_mul_func(&result, &temp, p, n0, num_limbs, log_limb_size, nsafe);
        }
        temp = mont_mul_func(&temp, &temp, p, n0, num_limbs, log_limb_size, nsafe);
        s = bigint::div2(&s, log_limb_size);
    }
    result
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
        mont_mul_modified,
        modpow,
        sqrt_case3mod4,
    };
    use num_bigint::{ BigUint, RandomBits };
    use num_traits::Zero;

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
        let mut rng = ChaCha8Rng::seed_from_u64(3u64);
        let p = BigUint::parse_bytes(b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);

        for log_limb_size in 12..14 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);
            for _ in 0..100 {
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
        let mut rng = ChaCha8Rng::seed_from_u64(3u64);
        let p = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);

        for log_limb_size in 12..14 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);
            for _ in 0..100 {
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
        let mut rng = ChaCha8Rng::seed_from_u64(3u64);
        let p = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);

        for log_limb_size in 14..16 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);
            for _ in 0..100 {
                let a: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                let b: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                mont_mul_modified_test(&a, &b, &p, num_limbs, log_limb_size);
            }
        }
    }

    #[test]
    pub fn test_bls12_377_mont_mul_modified_rand() {
        let mut rng = ChaCha8Rng::seed_from_u64(3u64);
        let p = BigUint::parse_bytes(b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
        let p_bitwidth = calc_bitwidth(&p);

        for log_limb_size in 14..16 {
            let num_limbs = calc_num_limbs(log_limb_size, p_bitwidth);
            for _ in 0..100 {
                let a: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                let b: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                mont_mul_modified_test(&a, &b, &p, num_limbs, log_limb_size);
            }
        }
    }

    #[test]
    pub fn test_biguint_pow() {
        let log_limb_size = 13;
        let num_limbs = calc_num_limbs(log_limb_size, 256);
        let p = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16).unwrap();
        let r = calc_mont_radix(num_limbs, log_limb_size);
        let x = BigUint::from(123u32);
        let xr = &x * &r % &p;
        let res = calc_rinv_and_n0(&p, &r, log_limb_size);
        let rinv = res.0;
        let exponent = (&p + BigUint::from(1u32)) / BigUint::from(4u32);

        // modpow for x which is not in Montgomery form
        let mut result = BigUint::from(1u32);
        let mut temp = x.clone();
        let mut s = exponent.clone();
        let two = BigUint::from(2u32);

        while !s.is_zero() {
            if &s % &two == BigUint::from(1u32) {
                result = &result * &temp % &p;
            }
            temp = &temp * &temp % &p;
            s = &s / &two;
        }

        let sqrt_x = result.clone();
        assert_eq!(sqrt_x, BigUint::parse_bytes(b"28187153645277682611288668793117688373912001564101965268716167503563995923543", 10).unwrap());

        // modpow for xr which is in Montgomery form
        let mut result = &r % &p;
        let mut temp = xr.clone();
        let mut s = exponent.clone();
        let two = BigUint::from(2u32);

        while !s.is_zero() {
            if &s % &two == BigUint::from(1u32) {
                result = (&result * &temp * &rinv) % &p;
            }
            temp = (&temp * &temp * &rinv) % &p;
            s = &s / &two;
        }
        // sqrt(xr) = (xr)^((p + 1) / 4) mod p
    }

    #[test]
    pub fn test_sqrt_case3mod4() {
        // Given xr, find sqrt(x)r
        // Note that sqrt(xy) = sqrt(x) * sqrt(y)
        //
        // sqrt(xr) = sqrt(x) * sqrt(r)
        // sqrt(x)r = sqrt(x) * sqrt(r) * sqrt(r) * r
        //
        //  Requires one ff::mul
        //  1. implement sqrt using Fq and test if it works for values in Montgomery form
        //  2. implement ff::mul
        let mut rng = ChaCha8Rng::seed_from_u64(3u64);
        let p = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16).unwrap();
        let exponent = (&p + BigUint::from(1u32)) / BigUint::from(4u32);

        for log_limb_size in 12..15 {
            let num_limbs = calc_num_limbs(log_limb_size, 256);

            let p_limbs = bigint::from_biguint_le(&p, num_limbs, log_limb_size);
            let exponent_limbs = bigint::from_biguint_le(&exponent, num_limbs, log_limb_size);

            let nsafe = calc_nsafe(log_limb_size);
            let r = calc_mont_radix(num_limbs, log_limb_size);
            let r_limbs = bigint::from_biguint_le(&(&r % &p), num_limbs, log_limb_size);

            let res = calc_rinv_and_n0(&p, &r, log_limb_size);
            let rinv = res.0;
            let n0 = res.1;

            for _ in 0..10 {
                let s: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256)) % &p;
                let x = &s * &s % &p;

                let sqrt_x = x.modpow(&exponent, &p);
                let sqrt_x_b = &p - &sqrt_x % &p;

                assert_eq!(&sqrt_x * &sqrt_x % &p, x);
                assert_eq!(&sqrt_x_b * &sqrt_x_b % &p, x);

                let xr = &x * &r % &p;
                let xr_limbs = bigint::from_biguint_le(&xr, num_limbs, log_limb_size);

                let expected_sqrt_xr = xr.modpow(&exponent, &p);
                // sqrt(xr) * sqrt(xr) == xr
                assert_eq!(&expected_sqrt_xr * &expected_sqrt_xr % &p, xr);

                // Compute sqrt(xr)
                let sqrt_xr_limbs = modpow(&xr_limbs, &r_limbs, &exponent_limbs, &p_limbs, n0, num_limbs, log_limb_size, nsafe);
                let sqrt_xr = bigint::to_biguint_le(&sqrt_xr_limbs, num_limbs, log_limb_size);

                assert_eq!((&sqrt_xr * &rinv) * (&sqrt_xr * &rinv) % &p, x);

                // Compute sqrt(x)r
                let sqrt_x_r_limbs = sqrt_case3mod4(&xr_limbs, &p_limbs, &r_limbs, n0, num_limbs, log_limb_size, nsafe);

                let s_a = bigint::to_biguint_le(&sqrt_x_r_limbs.0, num_limbs, log_limb_size);
                let s_b = bigint::to_biguint_le(&sqrt_x_r_limbs.1, num_limbs, log_limb_size);

                // sqrt(x)r * rinv * sqrt(x) == x
                assert_eq!(&s_a * &rinv * &sqrt_x % &p, x);
                assert_eq!(&s_b * &rinv * (&p - &sqrt_x) % &p, x);
            }
        }
    }
}

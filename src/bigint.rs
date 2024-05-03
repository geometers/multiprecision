use num_bigint::BigUint;
use num_traits::identities::Zero;
use std::num::Wrapping;

/// Converts a num_bigint::BigUint into a vector of limbs.
pub fn from_biguint_le(val: &BigUint, num_limbs: usize, log_limb_size: u32) -> Vec<u32> {
    let mut res = vec![0u32; num_limbs];
    let mask_u32 = 2u32.pow(log_limb_size as u32) - 1u32;
    let mask = BigUint::from(mask_u32);

    for i in 0..num_limbs {
        let idx = num_limbs - 1 - i;
        let shift = (idx as u32) * log_limb_size;
        let w = (val.clone() >> shift) & mask.clone();

        if !w.is_zero() {
            res[idx] = w.to_u32_digits()[0];
        }
    }

    res
}

/// Converts a vector of limbs into a num_bigint::BigUint.
pub fn to_biguint_le(limbs: &Vec<u32>, num_limbs: usize, log_limb_size: u32) -> BigUint {
    assert!(limbs.len() == num_limbs);
    let mut res = BigUint::from(0u32);
    let max = 2u32.pow(log_limb_size);

    for i in 0..num_limbs {
        assert!(limbs[i] < max);
        let idx = (num_limbs - 1 - i) as u32;
        let a = idx * log_limb_size;
        let b = BigUint::from(2u32).pow(a) * BigUint::from(limbs[idx as usize]);

        res += BigUint::from(b);
    }

    res
}

/// Returns a vector of zeros.
pub fn zero(num_limbs: usize) -> Vec<u32> {
    vec![0u32; num_limbs]
}

/// Returns lhs == rhs.
pub fn eq(lhs: &Vec<u32>, rhs: &Vec<u32>) -> bool {
    lhs == rhs
}

/// Returns lhs >= rhs. lhs and rhs must have the same length.
pub fn gte(lhs: &Vec<u32>, rhs: &Vec<u32>) -> bool {
    let num_limbs = rhs.len();
    assert!(lhs.len() == num_limbs);

    for idx in 0..num_limbs {
        let i = num_limbs - 1 - idx;
        if lhs[i] < rhs[i] {
            return false;
        } else if lhs[i] > rhs[i] {
            return true;
        }
    }
    true
}

/// Returns lhs > rhs. lhs and rhs must have the same length.
pub fn gt(lhs: &Vec<u32>, rhs: &Vec<u32>) -> bool {
    let num_limbs = rhs.len();
    assert!(lhs.len() == num_limbs);

    for idx in 0..num_limbs {
        let i = num_limbs - 1 - idx;
        if lhs[i] < rhs[i] {
            return false;
        } else if lhs[i] > rhs[i] {
            return true;
        }
    }
    false
}

/// Returns the sum of lhs and rhs. lhs and rhs must have the same length, and the result will have
/// one more digit than lhs.
///
/// # Arguments
/// 
/// * `lhs` - the left term
/// * `rhs` - the right term
pub fn add_wide(lhs: &Vec<u32>, rhs: &Vec<u32>, log_limb_size: u32) -> Vec<u32> {
    let num_limbs = rhs.len();
    assert!(lhs.len() == num_limbs);

    let mask = 2u32.pow(log_limb_size as u32) - 1u32;
    let mut res = vec![0u32; num_limbs + 1];
    let mut carry = 0u32;

    for i in 0..num_limbs {
        let c = lhs[i] + rhs[i] + carry;
        res[i] = c & mask;
        carry = c >> log_limb_size;
    }
    res[num_limbs] = carry;

    res
}

/// Returns the sum of lhs and rhs. lhs and rhs must have the same length. This function assumes
/// that the result will not overflow. If the sum of lhs and rhs have more digits than lhs, the
/// result will be incorrect.
///
/// # Arguments
/// 
/// * `lhs` - the left term
/// * `rhs` - the right term
pub fn add_unsafe(lhs: &Vec<u32>, rhs: &Vec<u32>, log_limb_size: u32) -> Vec<u32> {
    let num_limbs = rhs.len();
    assert!(lhs.len() == num_limbs);

    let mask = 2u32.pow(log_limb_size as u32) - 1u32;
    let mut res = vec![0u32; num_limbs];
    let mut carry = 0u32;

    for i in 0..num_limbs {
        let c = lhs[i] + rhs[i] + carry;
        res[i] = c & mask;
        carry = c >> log_limb_size;
    }

    res
}

/// Returns the subtraction of rhs from lhs. lhs and rhs must have the same length. This function
/// assumes that rhs is smaller than lhs. If this is not the case, the
/// result will be incorrect.
///
/// # Arguments
/// 
/// * `lhs` - the left term (minuend)
/// * `rhs` - the right term (subtrahend)
pub fn sub_with_borrow(lhs: &Vec<u32>, rhs: &Vec<u32>, log_limb_size: u32) -> (Vec<u32>, u32) {
    let num_limbs = rhs.len();
    assert!(lhs.len() == num_limbs);

    let mut w_borrow = Wrapping(0u32);
    let mut res = vec![0u32; num_limbs];

    let two_pow_word_size = Wrapping(2u32.pow(log_limb_size));

    for i in 0..num_limbs {
        let w_lhs = Wrapping(lhs[i]);
        let w_rhs = Wrapping(rhs[i]);

        res[i] = (w_lhs - w_rhs - w_borrow).0;

        if lhs[i] < (w_rhs + w_borrow).0 {
            res[i] = (Wrapping(res[i]) + two_pow_word_size).0;
            w_borrow = Wrapping(1u32);
        } else {
            w_borrow = Wrapping(0u32);
        }
    }
 
    (res, w_borrow.0)
}

pub fn sub(lhs: &Vec<u32>, rhs: &Vec<u32>, log_limb_size: u32) -> Vec<u32> {
    sub_with_borrow(lhs, rhs, log_limb_size).0
}

/// Returns v / 2
pub fn div2(v: &Vec<u32>, log_limb_size: u32) -> Vec<u32> {
    let mut result = vec![0u32; v.len()];

    let mut rem = 0u32;

    let m = 2u32.pow(log_limb_size);

    for idx in 0..v.len() {
        let i = v.len() - idx - 1;

        let d = v[i] + rem * m;
        let q = d / 2u32;
        rem = d % 2u32;
        result[i] = q;
    }

    result
}

pub fn mul(lhs: &Vec<u32>, rhs: &Vec<u32>, log_limb_size: u32) -> Vec<u32> {
    let num_words = lhs.len();
    assert_eq!(rhs.len(), num_words);

    let w_mask = (1u32 << log_limb_size) - 1u32;

    let mut res = vec![0u32; num_words * 2];
    for i in 0..num_words {
        for j in 0..num_words {
            let c = lhs[i] * rhs[j];
            res[i + j] += c & w_mask;
            res[i + j + 1] += c >> log_limb_size;
        }
    }

    for i in 0..(num_words * 2 - 1) {
        res[i + 1] += res[i] >> log_limb_size;
        res[i] = res[i] & w_mask;
    }

    res
}

/*
fn mul(a: ptr<function, BigInt>, b: ptr<function, BigInt>) -> BigIntWide {
    var res: BigIntWide;
    for (var i = 0u; i < NUM_WORDS; i = i + 1u) {
        for (var j = 0u; j < NUM_WORDS; j = j + 1u) {
            let c = (*a).limbs[i] * (*b).limbs[j];
            res.limbs[i+j] += c & W_MASK;
            res.limbs[i+j+1] += c >> WORD_SIZE;
        }   
    }

    /// Start from 0 and carry the extra over to the next index.
    for (var i = 0u; i < 2 * NUM_WORDS - 1; i = i + 1u) {
        res.limbs[i+1] += res.limbs[i] >> WORD_SIZE;
        res.limbs[i] = res.limbs[i] & W_MASK;
    }
    return res;
}
*/

pub fn is_even(val: &Vec<u32>) -> bool {
    val[0] % 2u32 == 0u32
}

pub fn is_zero(val: &Vec<u32>) -> bool {
    for i in 0..val.len() {
        if val[i] != 0u32 {
            return false;
        }
    }
    true
}

pub fn is_one(val: &Vec<u32>) -> bool {
    if val[0] != 1u32 {
        return false;
    }

    for i in 1..val.len() {
        if val[i] != 0u32 {
            return false;
        }
    }

    true
}

#[cfg(test)]
pub mod tests {
    use crate::bigint::{
        zero, eq, add_wide, add_unsafe, sub, div2, gt, gte, is_even, mul, from_biguint_le, to_biguint_le
    };
    use crate::utils::calc_num_limbs;
    use num_bigint::{ BigUint, RandomBits };
    use rand::Rng;
    use rand_chacha::ChaCha8Rng;
    use rand_chacha::rand_core::SeedableRng;

    #[test]
    pub fn test_is_even() {
        let log_limb_size = 13;
        let num_limbs = 20;

        for i in 0..16384 {
            let v = BigUint::from(i as u32);
            let v_limbs = from_biguint_le(&v, num_limbs, log_limb_size);

            assert_eq!(is_even(&v_limbs), i % 2 == 0);
        }
    }


    #[test]
    pub fn test_eq() {
        let a = vec![0, 0];
        let b = vec![0, 1];
        let c = vec![0, 1];
        let d = vec![0, 1];
        assert!(!eq(&a, &b));
        assert!(eq(&c, &d));
    }

    #[test]
    pub fn test_zero() {
        let len = 16;
        let z = zero(len);
        for limb in &z {
            assert!(*limb == 0u32);
        }
        assert!(z.len() == len);
    }

    #[test]
    pub fn test_add_wide() {
        let a = vec![5u32, 1u32];
        let b = vec![5u32, 1u32];
        let c = add_wide(&a, &b, 3);
        let expected = vec![2u32, 3u32, 0u32];
        assert!(eq(&c, &expected));
    }

    #[test]
    pub fn test_add_wide_2() {
        let num_limbs = 20;
        let log_limb_size = 13;
        let a = BigUint::parse_bytes(b"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16).unwrap();
        let b = BigUint::parse_bytes(b"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16).unwrap();
        let a_limbs = from_biguint_le(&a, num_limbs, log_limb_size);
        let b_limbs = from_biguint_le(&a, num_limbs, log_limb_size);
        let c_limbs = add_wide(&a_limbs, &b_limbs, log_limb_size);
        let c = to_biguint_le(&c_limbs, num_limbs + 1, log_limb_size);
        let expected = &a + &b;
        let expected_limbs = from_biguint_le(&expected, num_limbs + 1, log_limb_size);

        assert!(eq(&c_limbs, &expected_limbs));
        assert!(c == expected);
    }

    #[test]
    pub fn test_add_unsafe() {
        let a = vec![5u32, 1u32];
        let b = vec![5u32, 1u32];
        let c = add_unsafe(&a, &b, 3);
        let expected = vec![2u32, 3u32];
        assert!(eq(&c, &expected));
    }

    #[test]
    pub fn test_add_unsafe2() {
        let a = vec![2u32, 1u32];
        let b = vec![2u32, 1u32];
        let c = add_unsafe(&a, &b, 3);
        let expected = vec![4u32, 2u32];
        assert!(eq(&c, &expected));
    }

    #[test]
    pub fn test_sub() {
        let a = vec![5u32, 1u32];
        let b = vec![5u32, 1u32];
        let c = sub(&a, &b, 3);
        assert!(eq(&c, &zero(2)));

        let d = vec![5u32, 1u32];
        let e = vec![4u32, 1u32];
        let f = sub(&d, &e, 3);
        assert!(eq(&f, &vec![1u32, 0u32]));
    }

    #[test]
    pub fn test_gt() {
        let a = vec![2u32, 1u32];
        let b = vec![2u32, 1u32];
        assert!(!gt(&a, &b));

        let c = vec![4u32, 1u32];
        let d = vec![2u32, 1u32];
        assert!(gt(&c, &d));

        let e = vec![4u32, 0u32];
        let f = vec![4u32, 1u32];
        assert!(!gt(&e, &f));
    }

    #[test]
    pub fn test_gte() {
        let a = vec![2u32, 1u32];
        let b = vec![2u32, 1u32];
        assert!(gte(&a, &b));

        let c = vec![4u32, 1u32];
        let d = vec![2u32, 1u32];
        assert!(gte(&c, &d));

        let e = vec![4u32, 0u32];
        let f = vec![4u32, 1u32];
        assert!(!gte(&e, &f));
    }

    #[test]
    pub fn test_from_biguint_le() {
        let num_limbs = 3usize;
        let log_limb_size = 3u32;
        let p = BigUint::from(103u32);
        let p_limbs = from_biguint_le(&p, num_limbs, log_limb_size);
        assert!(eq(&p_limbs, &vec![7u32, 4u32, 1u32]));

        let p = BigUint::parse_bytes(b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
        let num_limbs = 20;
        let log_limb_size = 13u32;
        let p_limbs = from_biguint_le(&p, num_limbs, log_limb_size);
        let expected: Vec<u32> = vec![1, 0, 0, 768, 4257, 0, 0, 8154, 2678, 2765, 3072, 6255, 4581, 6694, 6530, 5290, 6700, 2804, 2777, 37];
        assert!(eq(&p_limbs, &expected));
    }

    #[test]
    pub fn test_to_biguint_le() {
        let num_limbs = 3usize;
        let log_limb_size = 3u32;
        let val = vec![7u32, 4u32, 1u32];
        let expected = BigUint::from(103u32);
        let res = to_biguint_le(&val, num_limbs, log_limb_size);
        assert!(res == expected);

        let expected = BigUint::parse_bytes(b"12ab655e9a2ca55660b44d1e5c37b00159aa76fed00000010a11800000000001", 16).unwrap();
        let limbs: Vec<u32> = vec![1, 0, 0, 768, 4257, 0, 0, 8154, 2678, 2765, 3072, 6255, 4581, 6694, 6530, 5290, 6700, 2804, 2777, 37];
        let res = to_biguint_le(&limbs, 20, 13);
        assert!(res == expected);
    }

    #[test]
    pub fn test_biguint_conversion() {
        let num_limbs = 4;
        let log_limb_size = 16;
        let max = 2u32.pow(log_limb_size);
        for i in 0..max {
            let p = BigUint::from(i);
            let limbs = from_biguint_le(&p, num_limbs, log_limb_size);
            let expected = to_biguint_le(&limbs, num_limbs, log_limb_size);
            assert!(p == expected);
        }

        let num_limbs = 5;
        let log_limb_size = 15;
        for i in 0..max {
            let p = BigUint::from(i);
            let limbs = from_biguint_le(&p, num_limbs, log_limb_size);
            let expected = to_biguint_le(&limbs, num_limbs, log_limb_size);
            assert!(p == expected);
        }
    }

    #[test]
    pub fn test_div2() {
        let mut rng = ChaCha8Rng::seed_from_u64(3 as u64);
        for log_limb_size in 11..16 {
            let num_limbs = calc_num_limbs(log_limb_size, 256);
            for _ in 0..100 {
                let a: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                let a_limbs = from_biguint_le(&a, num_limbs, log_limb_size);
                let result_limbs = div2(&a_limbs, log_limb_size);
                let result = to_biguint_le(&result_limbs, num_limbs, log_limb_size);

                assert_eq!(result, a / BigUint::from(2u32));
            }
        }
    }

    #[test]
    pub fn test_mul() {
        let mut rng = ChaCha8Rng::seed_from_u64(3 as u64);
        for log_limb_size in 11..16 {
            let num_limbs = calc_num_limbs(log_limb_size, 256);
            for _ in 0..100 {
                let a: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                let b: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256));
                let a_limbs = from_biguint_le(&a, num_limbs, log_limb_size);
                let b_limbs = from_biguint_le(&b, num_limbs, log_limb_size);

                let result_limbs = mul(&a_limbs, &b_limbs, log_limb_size);
                let result = to_biguint_le(&result_limbs, num_limbs * 2, log_limb_size);

                assert_eq!(result, a * b);
            }
        }
    }
}

use crate::bigint;

pub fn add(
    lhs: &Vec<u32>,
    rhs: &Vec<u32>,
    p: &Vec<u32>,
    log_limb_size: u32
) -> Vec<u32> {
    let num_limbs = lhs.len();
    assert!(lhs.len() == num_limbs);
    assert!(p.len() == num_limbs);

    let mut sum_wide = bigint::add_wide(&lhs, &rhs, log_limb_size);

    let mut p_wide = Vec::with_capacity(num_limbs + 1);

    for v in p {
        p_wide.push(v.clone());
    }
    p_wide.push(0u32);

    if bigint::gte(&sum_wide, &p_wide) {
        let mut s = bigint::sub(&sum_wide, &p_wide, log_limb_size);
        s.resize(num_limbs, 0u32);

        return s;
    }

    sum_wide.resize(num_limbs, 0u32);

    sum_wide
}

pub fn sub(
    lhs: &Vec<u32>,
    rhs: &Vec<u32>,
    p: &Vec<u32>,
    log_limb_size: u32
) -> Vec<u32> {
    if bigint::gte(lhs, rhs) {
        return bigint::sub(lhs, rhs, log_limb_size);
    }
    let r = bigint::sub(rhs, lhs, log_limb_size);

    bigint::sub(p, &r, log_limb_size)
}

/*
/// Calculates the Montgomery product of lhs and rhs. lhs and rhs must already be in Montgomery
/// form. For instance:
///
/// lhs = a * r
/// rhs = b * r
/// mont_mul(lhs, rhs) = a * b * r
/// 
/// Only limb sizes between ___ and ___ are supported.
pub fn mont_mul(
    lhs: Vec<u32>,
    rhs: Vec<u32>
    log_limb_size: u32
) {
    assert!(log_limb_size < 16);
    match log_limb_size {
        13 => mont_mul_optimised(lhs, rhs, log_limb_size),
        _ => panic!("unsupported limb size")
    }
}

pub fn mont_mul_optimised(
    lhs: Vec<u32>,
    rhs: Vec<u32>
    log_limb_size: u32
)
*/

#[cfg(test)]
pub mod tests {
    use crate::ff::{ add, sub };
    use crate::bigint;
    use num_bigint::BigUint;

    fn do_test_add(
        a: &BigUint,
        b: &BigUint,
        p: &BigUint,
        num_limbs: usize,
        log_limb_size: u32
    ) {
        let p_limbs = bigint::from_biguint_le(&p, num_limbs, log_limb_size);
        let a_limbs = bigint::from_biguint_le(&a, num_limbs, log_limb_size);
        let b_limbs = bigint::from_biguint_le(&b, num_limbs, log_limb_size);

        let sum_limbs = add(&a_limbs, &b_limbs, &p_limbs, log_limb_size);

        let sum = (a + b) % p;

        let expected = bigint::from_biguint_le(&sum, num_limbs, log_limb_size);

        assert!(bigint::eq(&sum_limbs, &expected));
    }

    fn do_test_sub(
        a: &BigUint,
        b: &BigUint,
        p: &BigUint,
        num_limbs: usize,
        log_limb_size: u32
    ) {
        let p_limbs = bigint::from_biguint_le(&p, num_limbs, log_limb_size);
        let a_limbs = bigint::from_biguint_le(&a, num_limbs, log_limb_size);
        let b_limbs = bigint::from_biguint_le(&b, num_limbs, log_limb_size);

        let sub_limbs = sub(&a_limbs, &b_limbs, &p_limbs, log_limb_size);

        let sub = if a >= b {
            a - b
        } else {
            let r = b - a;
            p - r
        };

        let expected = bigint::from_biguint_le(&sub, num_limbs, log_limb_size);

        assert!(bigint::eq(&sub_limbs, &expected));
    }

    #[test]
    pub fn test_add() {
        let num_limbs = 2;
        let log_limb_size = 3;

        let p = BigUint::from(15u32);
        let a = BigUint::from(7u32);
        let b = BigUint::from(7u32);

        do_test_add(&a, &b, &p, num_limbs, log_limb_size);

        let p = BigUint::from(15u32);
        let a = BigUint::from(8u32);
        let b = BigUint::from(8u32);

        do_test_add(&a, &b, &p, num_limbs, log_limb_size);
    }

    #[test]
    pub fn test_sub() {
        let num_limbs = 2;
        let log_limb_size = 3;

        let p = BigUint::from(15u32);
        let a = BigUint::from(7u32);
        let b = BigUint::from(7u32);

        do_test_sub(&a, &b, &p, num_limbs, log_limb_size);

        let p = BigUint::from(15u32);
        let a = BigUint::from(8u32);
        let b = BigUint::from(8u32);

        do_test_sub(&a, &b, &p, num_limbs, log_limb_size);
    }

    #[test]
    pub fn test_add_multi() {
        let num_limbs = 3;
        let log_limb_size = 4;
        let max = 2u32.pow(log_limb_size);

        for p in 2..max {
            let p_b = BigUint::from(p as u32);
            let p_limbs = bigint::from_biguint_le(&p_b, num_limbs, log_limb_size);
            for i in 0..p {
                let i_b = BigUint::from(i as u32);
                let i_limbs = bigint::from_biguint_le(&i_b, num_limbs, log_limb_size);

                for j in 0..p {
                    let j_b = BigUint::from(j as u32);
                    let j_limbs = bigint::from_biguint_le(&j_b, num_limbs, log_limb_size);

                    let expected = (&i_b + &j_b) % &p_b;
                    let expected_limbs = bigint::from_biguint_le(&expected, num_limbs, log_limb_size);
                    let res_limbs = add(&i_limbs, &j_limbs, &p_limbs, log_limb_size);

                    assert!(bigint::eq(&res_limbs, &expected_limbs));
                }
            }
        }
    }

    #[test]
    pub fn test_sub_multi() {
        let num_limbs = 3;
        let log_limb_size = 4;
        let max = 2u32.pow(log_limb_size);

        for p in 2..max {
            let p_b = BigUint::from(p as u32);
            let p_limbs = bigint::from_biguint_le(&p_b, num_limbs, log_limb_size);
            for i in 0..p {
                let i_b = BigUint::from(i as u32);
                let i_limbs = bigint::from_biguint_le(&i_b, num_limbs, log_limb_size);

                for j in 0..p {
                    let j_b = BigUint::from(j as u32);
                    let j_limbs = bigint::from_biguint_le(&j_b, num_limbs, log_limb_size);

                    let expected = if i_b >= j_b {
                        (&i_b - &j_b) % &p_b
                    } else {
                        &p_b - (&j_b - &i_b)
                    };

                    let expected_limbs = bigint::from_biguint_le(&expected, num_limbs, log_limb_size);
                    let res_limbs = sub(&i_limbs, &j_limbs, &p_limbs, log_limb_size);

                    assert!(bigint::eq(&res_limbs, &expected_limbs));
                }
            }
        }
    }
}

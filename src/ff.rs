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

/// Returns the modular inverse of x where the field modulus is p
pub fn inverse(
    x_limbs: &Vec<u32>, 
    p_limbs: &Vec<u32>, 
    num_limbs: usize,
    log_limb_size: u32
) -> Vec<u32> {
    let mut c = vec![0u32; num_limbs];
    let mut b = vec![0u32; num_limbs];
    b[0] = 1u32;
    let mut u = x_limbs.clone();
    let mut v = p_limbs.clone();

    while !bigint::is_one(&u) && !bigint::is_one(&v) {
        while bigint::is_even(&u) {
            u = bigint::div2(&u, log_limb_size);
            if bigint::is_even(&b) {
                b = bigint::div2(&b, log_limb_size);
            } else {
                // TODO: find out if add_unsafe is OK here
                let bp = bigint::add_unsafe(&b, p_limbs, log_limb_size);
                b = bigint::div2(&bp, log_limb_size);
            }
        }

        while bigint::is_even(&v) {
            v = bigint::div2(&v, log_limb_size);
            if bigint::is_even(&c) {
                c = bigint::div2(&c, log_limb_size);
            } else {
                // TODO: find out if add_unsafe is OK here
                let cp = bigint::add_unsafe(&c, p_limbs, log_limb_size);
                c = bigint::div2(&cp, log_limb_size);
            }
        }

        if bigint::gte(&u, &v) {
            u = sub(&u, &v, &p_limbs, log_limb_size);
            b = sub(&b, &c, &p_limbs, log_limb_size);
        } else {
            v = sub(&v, &u, &p_limbs, log_limb_size);
            c = sub(&c, &b, &p_limbs, log_limb_size);
        }
    }

    let mut result = if bigint::is_one(&u) {
        b
    } else {
        c
    };

    if bigint::gte(&result, &p_limbs) {
        result = bigint::sub(&result, &p_limbs, log_limb_size);
    }

    result
}

#[cfg(test)]
pub mod tests {
    use crate::ff::{ add, sub, inverse };
    use crate::utils::calc_num_limbs;
    use crate::bigint;
    use num_bigint::{ BigUint, RandomBits };
    use rand::Rng;
    use rand_chacha::ChaCha8Rng;
    use rand_chacha::rand_core::SeedableRng;
    use rayon::prelude::*;

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

    #[test]
    pub fn test_inverse() {
        let p = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16).unwrap();
        let mut rng = ChaCha8Rng::seed_from_u64(3 as u64);

        for log_limb_size in 11..16 {
            let num_limbs = calc_num_limbs(log_limb_size, 256);

            let x: BigUint = rng.sample::<BigUint, RandomBits>(RandomBits::new(256)) % &p;
            (0..100).into_par_iter().for_each(|i| {
                let x = &x * BigUint::from((i + 1) as u32) % &p;

                let res = crate::mont::calc_inv_and_pprime(&p, &x);
                let x_inv = res.0;
                let x_inv_limbs = bigint::from_biguint_le(&x_inv, num_limbs, log_limb_size);

                assert_eq!(&x * &x_inv % &p, BigUint::from(1u32));

                let x_limbs = bigint::from_biguint_le(&x, num_limbs, log_limb_size);

                let p_limbs = bigint::from_biguint_le(&p, num_limbs, log_limb_size);

                let inverse_limbs = inverse(&x_limbs, &p_limbs, num_limbs, log_limb_size);

                assert_eq!(inverse_limbs, x_inv_limbs);
            });
        }
    }
}

// Converts a slice of 34 bytes to a Vec of 32 16-bit values
pub fn bytes_34_to_limbs_32(a: &[u8]) -> Vec<u32> {
    assert_eq!(a.len(), 34);
    let mut res = vec![0u32; 32];

    for i in 0..17 {
        res[16 - i] = ((a[i * 2] as u32) << 8) + a[i * 2 + 1] as u32;
    }

    res
}

#[cfg(test)]
pub mod tests {
    use rand::RngCore;
    use rand_chacha::ChaCha8Rng;
    use rand_chacha::rand_core::SeedableRng;
    use num_bigint::BigUint;
    use rayon::prelude::{IntoParallelIterator, ParallelIterator};
    use crate::bigint;
    use crate::utils::biguint_to_bytes_be;
    use crate::reduce::bytes_34_to_limbs_32;

    pub fn num_bits(
        x: &BigUint,
    ) -> usize {
        x.to_bytes_be().len() * 8
    }

    // Converts a slice of 64 bytes to a Vec of 32 16-bit values
    pub fn bytes_64_to_limbs_16(a: &[u8]) -> Vec<u32> {
        assert_eq!(a.len(), 64);
        let mut res = vec![0u32; 32];
        for i in 0..32 {
            res[31 - i] = ((a[i * 2] as u32) << 8) + a[i * 2 + 1] as u32;
        }
        res
    }

    // Converts a slice of 32 bytes to a Vec of 32 16-bit values
    pub fn bytes_32_to_limbs_32(a: &[u8]) -> Vec<u32> {
        assert_eq!(a.len(), 32);
        let mut res = vec![0u32; 32];
        for i in 0..16 {
            res[15 - i] = ((a[i * 2] as u32) << 8) + a[i * 2 + 1] as u32;
        }
        res
    }

    pub fn shr_512(a: &Vec<u32>) -> Vec<u32> {
        assert_eq!(a.len(), 64);
        a[32..64].to_vec()
    }

    /// Barrett reduction based on https://www.nayuki.io/page/barrett-reduction-algorithm
    pub fn barrett_nayuki(
        x: &BigUint,
        p: &BigUint,
    ) -> BigUint {
        let k = 512u32;
        let b = 2u32;
        let precomputed_r = BigUint::from(b).pow(k) / p;

        // The precomputed r = (b^k) / p
        let r = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffeb2106215d086329a7ed9ce5a30a2c131b", 16).unwrap();
        assert_eq!(r, precomputed_r);

        let r_bytes = biguint_to_bytes_be(&r, 34);
        let x_bytes = biguint_to_bytes_be(&x, 64);
        let p_bytes = biguint_to_bytes_be(&p, 32);

        // r and x as 32 16-bit limbs.
        // TODO: write a mul() which takes as input a list of 16 16-bit
        // limbs and a list of 32 16-bit limbs.
        let r_limbs = bytes_34_to_limbs_32(&r_bytes);
        let x_limbs = bytes_64_to_limbs_16(&x_bytes);
        let p_limbs = bytes_32_to_limbs_32(&p_bytes);

        // Compute x * r
        let xr_limbs = bigint::mul(&r_limbs, &x_limbs, 16);

        // Sanity check for x * r
        let xr_biguint = bigint::to_biguint_le(&xr_limbs, 64, 16);
        let xr = x * &r;
        assert_eq!(xr_biguint, xr);

        // Shift xr right by 512 bits
        let xr_shr_512_limbs = shr_512(&xr_limbs);

        // Sanity check for shr_512(xr)
        let xr_shr = &xr >> 512u32;

        assert_eq!(xr_shr, bigint::to_biguint_le(&xr_shr_512_limbs, 32, 16));

        // Compute xr_shr * p
        let xr_shr_p = &xr_shr * p;

        let xr_shr_512_p_limbs = bigint::mul(&xr_shr_512_limbs, &p_limbs, 16);

        // Sanity check of xr * p
        assert_eq!(xr_shr_p, bigint::to_biguint_le(&xr_shr_512_p_limbs, 64, 16));

        // Take the first 32 limbs of xr_shr_512_p
        let rhs_limbs = Vec::<u32>::from(&xr_shr_512_p_limbs[0..32]);

        // Compute x - rhs
        let mut t_limbs = bigint::sub(&x_limbs, &rhs_limbs, 16);
        let t = x - xr_shr_p;
        assert_eq!(t, bigint::to_biguint_le(&t_limbs, 32, 16));

        // Conditional reduction
        while bigint::gte(&t_limbs, &p_limbs) {
            t_limbs = bigint::sub(&t_limbs, &p_limbs, 16);
        }

        bigint::to_biguint_le(&t_limbs, 32, 16)
    }

    pub fn barrett_nayuki_biguint(
        x: &BigUint,
        p: &BigUint,
    ) -> BigUint {
        // TODO: figure out and prove why these numbers work
        let k: u32 = 256;
        //let b: u32 = 2;

        // Precomputed
        let m = BigUint::from(4u32).pow(k);
        let r = &m / p;

        let xr = x * &r;

        let xr_shr = &xr >> (2 * k);

        let rhs = xr_shr * p;

        let t = x - rhs;
        //let t = x - (&xr / &m) * p;

        let mut result = t.clone();

        let mut i = 0;
        while result > *p {
            i += 1;
            result = &result - p;
            //println!("i: {}", i);
        }

        if i > 1 {
            //println!("x: {}", x);
            println!("i: {}", i);
        }

        result
    }

    /// https://eprint.iacr.org/2022/411.pdf
    pub fn barrett_greuet_et_al_biguint(
        x: &BigUint,
        p: &BigUint,
    ) -> BigUint {
        // Select a k such that 2^k > x. Since x is a 512-bit value, its maximum value is 2^512 -
        // 1, so k can be 512
        let k = 512;
        let r = BigUint::from(2u32).pow(k) / p;
        let xr = x * &r;
        let xr_shr = xr >> k;
        let rhs = xr_shr * p;

        let t = x - rhs;

        let mut result = t.clone();

        let mut i = 0;
        while result > *p {
            i += 1;
            result = &result - p;
            //println!("i: {}", i);
        }

        if i > 1 {
            //println!("x: {}", x);
            println!("i: {}", i);
        }

        result
    }

    pub fn do_test(val: &BigUint, p: &BigUint) {
        // Test with x and x % p
        let y = val % p;

        for x in &[val.clone(), y.clone()] {
            let reduced = x % p;

            let result_nayuki_biguint = barrett_nayuki_biguint(&x, &p);
            assert_eq!(result_nayuki_biguint, reduced);

            let result_nayuki = barrett_nayuki(&x, &p);
            assert_eq!(result_nayuki, reduced);

            let result_greuet_et_al_biguint = barrett_greuet_et_al_biguint(&x, &p);
            assert_eq!(result_greuet_et_al_biguint, reduced);
        }
    }

    #[test]
    pub fn test_barrett_reduction() {
        let p = BigUint::parse_bytes(b"1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed", 16).unwrap();

        // Generate a random input

        (0..1000).into_par_iter().for_each(|i| {
            let mut rng = ChaCha8Rng::seed_from_u64(i as u64);
            let mut input = [0u8; 64];
            rng.fill_bytes(&mut input);
            let x = BigUint::from_bytes_be(&input);

            do_test(&x, &p);
        });

        /*
        // From the Handbook of Applied Cryptography
        let k = 128u32;
        let b = BigUint::from(4u32);
        let u = b.pow(k * 2) / &p;
        let bkp1 = b.pow(k + 1);
        let bkm1 = b.pow(k - 1);

        let q1 = &x / &bkm1;
        let q2 = q1 * u;
        let q3 = q2 / &bkp1;

        let r1 = &x % &bkp1;
        let r2 = (&q3 * &p) % &bkp1;

        let mut result = if r1 < r2 {
            &r1 + &bkp1 - &r2 
        } else {
            &r1 - &r2
        };

        while result >= p {
            result = result - &p;
        }

        println!("result  : {}", result);
        println!("expected: {}", reduced);
        */
    }
}

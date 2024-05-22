#[cfg(test)]
pub mod tests {
    use rand::RngCore;
    use rand_chacha::ChaCha8Rng;
    use rand_chacha::rand_core::SeedableRng;
    use sha2::Digest;
    use num_bigint::BigUint;
    use rayon::prelude::{IntoParallelIterator, ParallelIterator};
    use crate::bigint;
    use crate::sha512::sha512_96;
    use crate::utils::bytes_to_u32s_be;

    pub fn num_bits(
        x: &BigUint,
    ) -> usize {
        x.to_bytes_be().len() * 8
    }

    // Converts a slice of 34 bytes to a Vec of 32 16-bit values
    pub fn bytes_34_to_limbs_32(a: &[u8]) -> Vec<u32> {
        assert_eq!(a.len(), 34);
        let mut res = vec![0u32; 32];

        let mut b = a.to_vec();

        for i in 0..17 {
            res[16 - i] = ((b[i * 2] as u32) << 8) + b[i * 2 + 1] as u32;
        }

        res
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

    pub fn shr_520(a: &Vec<u32>) -> Vec<u32> {
        assert_eq!(a.len(), 64);
        let mut limbs = a[32..64].to_vec();
        let mut result = vec![0u32; 32];
        let mut i = 0;
        for i in 0..17 {
            result[i] = (limbs[i] >> 8) + ((limbs[i + 1] & 0xff) << 8);
        }
        result
    }

    pub fn biguint_to_bytes_be(x: &BigUint, num_bytes: usize) -> Vec<u8> {
        let mut bytes = x.to_bytes_be().to_vec();
        while bytes.len() < num_bytes {
            bytes.insert(0, 0u8);
        }
        bytes
    }

    /// Barrett reduction based on https://www.nayuki.io/page/barrett-reduction-algorithm
    pub fn barrett_nayuki(
        x: &BigUint,
        p: &BigUint,
    ) -> BigUint {
        let log_limb_size = 32;
        let num_limbs = 8;

        // The precomputed r = (b^k) / p
        let r = BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffeb2106215d086329a7ed9ce5a30a2c131b39", 16).unwrap();

        let r_bytes = biguint_to_bytes_be(&r, 34);
        let x_bytes = biguint_to_bytes_be(&x, 64);
        let p_bytes = biguint_to_bytes_be(&p, 32);

        // r and x as 32 16-bit limbs.
        // TODO: write a mul() which takes as input a list of 16 16-bit
        // limbs and a list of 32 16-bit limbs.
        let r_limbs_16 = bytes_34_to_limbs_32(&r_bytes);
        let r_biguint = bigint::to_biguint_le(&r_limbs_16, 32, 16);

        let x_limbs_16 = bytes_64_to_limbs_16(&x_bytes);

        // Compute x * r
        let xr_limbs_16 = bigint::mul(&r_limbs_16, &x_limbs_16, 16);

        // Sanity check for x * r
        let xr_biguint = bigint::to_biguint_le(&xr_limbs_16, 64, 16);
        let xr = x * &r;
        assert_eq!(xr_biguint, xr);

        // Shift xr right by 520 bits
        let xr_shr_520 = shr_520(&xr_limbs_16);

        // Sanity check for shr_520(xr)
        let xr_shr = &xr >> 520u32;

        assert_eq!(xr_shr, bigint::to_biguint_le(&xr_shr_520, 32, 16));

        // Compute xr_shr * p
        let xr_shr_p = &xr_shr * p;

        let p_limbs = bytes_32_to_limbs_32(&p_bytes);
        let xr_shr_520_p_limbs = bigint::mul(&xr_shr_520, &p_limbs, 16);

        // Sanity check of xr * p
        assert_eq!(xr_shr_p, bigint::to_biguint_le(&xr_shr_520_p_limbs, 64, 16));

        // Take the first 32 limbs of xr_shr_520_p
        let rhs_limbs = Vec::<u32>::from(&xr_shr_520_p_limbs[0..32]);

        // Compute x - rhs
        let mut t_limbs = bigint::sub(&x_limbs_16, &rhs_limbs, 16);
        let t = x - xr_shr_p;
        assert_eq!(t, bigint::to_biguint_le(&t_limbs, 32, 16));

        // Conditional reduction
        while bigint::gte(&t_limbs, &p_limbs) {
            t_limbs = bigint::sub(&t_limbs, &p_limbs, 16);
        }

        let t = bigint::to_biguint_le(&t_limbs, 32, 16);
        t
    }

    pub fn barrett_nayuki_biguint(
        x: &BigUint,
        p: &BigUint,
    ) -> BigUint {
        // TODO: figure out and prove why these numbers work
        let k = 104u32;
        let b = 32u32;

        // Precomputed
        let m = BigUint::from(b).pow(k);
        let r = &m / p;

        let xr = x * &r;

        let xr_shr = &xr >> 520u32;

        let rhs = xr_shr * p;

        let t = x - rhs;
        //let t = x - (&xr / &m) * p;

        let mut result = t.clone();

        let mut i = 0;
        while result > *p {
            i += 1;
            result = &result - p;
        }

        if i > 1 {
            println!("x: {}", x);
            println!("i: {}", i);
        }

        result
    }

    #[test]
    pub fn test_barrett_reduction() {
        let p = BigUint::parse_bytes(b"1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed", 16).unwrap();

        // Generate a random input

        //(0..100000000).into_par_iter().for_each(|i| {
        (0..1000).into_par_iter().for_each(|i| {
            let mut rng = ChaCha8Rng::seed_from_u64(i as u64);
            let mut input = [0u8; 64];
            rng.fill_bytes(&mut input);
            let x = BigUint::from_bytes_be(&input);

            let reduced = &x % &p;

            let result_nayuki_biguint = barrett_nayuki_biguint(&x, &p);
            assert_eq!(result_nayuki_biguint, reduced);

            let result_nayuki = barrett_nayuki(&x, &p);
            assert_eq!(result_nayuki, reduced);
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

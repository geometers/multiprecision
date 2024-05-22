use crate::utils::bytes_to_u32s_be;

/// A custom SHA512 hash function that accepts a 96-byte input.
/// Based on https://gist.github.com/illia-v/7883be942da5d416521375004cecb68f
pub fn sha512_96(
    input_bytes: &[u8; 96],
    ) -> [u8; 64] {
    // Convert input_bytes to machine words (Vec::<u32>)
    let mut message_array = bytes_to_u32s_be(input_bytes.as_slice());

    // Pad the input to get the message array.
    let padding = bytes_to_u32s_be(
        &hex::decode("8000000000000000000000000000000000000000000000000000000000000300").unwrap()
    );

    message_array.extend(padding);

    let rc = round_constants();

    let mut sha512_hash = initial_hash();

    // The message schedule (160 32-bit words)
    let mut w = vec![0u32; 160];

    // For t = 0 to 32: Wt = M(i)t
    for t in 0..message_array.len() {
        w[t] = message_array[t]
    }

    for i in 16..80 {
        let wim15 = (w[(i * 2) - 30], w[(i * 2) - 29]);
        let wim2 = (w[(i * 2) - 4], w[(i * 2) - 3]);
        let wim16 = (w[(i * 2) - 32], w[(i * 2) - 31]);
        let wim7 = (w[(i * 2) - 14], w[(i * 2) - 13]);

        let s0 = xor(xor(right_rotate(wim15, 1), right_rotate(wim15, 8)), shr(wim15, 7));
        let s1 = xor(xor(right_rotate(wim2, 19), right_rotate(wim2, 61)), shr(wim2, 6));

        let rr = and(add(add(add(wim16, s0), wim7), s1), (0xffffffff, 0xffffffff));
        w[i * 2] = rr.0;
        w[i * 2 + 1] = rr.1;
    }
    let mut a = sha512_hash[0];
    let mut b = sha512_hash[1];
    let mut c = sha512_hash[2];
    let mut d = sha512_hash[3];
    let mut e = sha512_hash[4];
    let mut f = sha512_hash[5];
    let mut g = sha512_hash[6];
    let mut h = sha512_hash[7];

    for i in 0..80 {
        let sum1 = xor(xor(right_rotate(e, 14), right_rotate(e, 18)), right_rotate(e, 41));
        let ch = xor(
            and(e, f),
            and(not(e), g)
            );
        let temp1 = add(add(add(add(h, sum1), ch), rc[i]), (w[i * 2], w[i * 2 + 1]));
        let sum0 = xor(xor(right_rotate(a, 28), right_rotate(a, 34)), right_rotate(a, 39));
        let maj = xor(xor(and(a, b), and(a, c)), and(b, c));
        let temp2 = add(sum0, maj);
        h = g;
        g = f;
        f = e;
        e = add(d, temp1);
        d = c;
        c = b;
        b = a;
        a = add(temp1, temp2);
    }

    let lhs = &[a, b, c, d, e, f, g, h];
    for j in 0..8 {
        sha512_hash[j] = add(sha512_hash[j], lhs[j]);
    }

    let result = words_to_bytes_be(&sha512_hash);
    result.as_slice().try_into().unwrap()
}

pub fn initial_hash() -> Vec<(u32, u32)> {
    bytes_to_words_be(&hex::decode("6a09e667f3bcc908bb67ae8584caa73b3c6ef372fe94f82ba54ff53a5f1d36f1510e527fade682d19b05688c2b3e6c1f1f83d9abfb41bd6b5be0cd19137e2179").unwrap())
}

pub fn round_constants() -> Vec<(u32, u32)> {
    bytes_to_words_be(
        &hex::decode(
            "428a2f98d728ae227137449123ef65cdb5c0fbcfec4d3b2fe9b5dba58189dbbc3956c25bf348b53859f111f1b605d019923f82a4af194f9bab1c5ed5da6d8118d807aa98a303024212835b0145706fbe243185be4ee4b28c550c7dc3d5ffb4e272be5d74f27b896f80deb1fe3b1696b19bdc06a725c71235c19bf174cf692694e49b69c19ef14ad2efbe4786384f25e30fc19dc68b8cd5b5240ca1cc77ac9c652de92c6f592b02754a7484aa6ea6e4835cb0a9dcbd41fbd476f988da831153b5983e5152ee66dfaba831c66d2db43210b00327c898fb213fbf597fc7beef0ee4c6e00bf33da88fc2d5a79147930aa72506ca6351e003826f142929670a0e6e7027b70a8546d22ffc2e1b21385c26c9264d2c6dfc5ac42aed53380d139d95b3df650a73548baf63de766a0abb3c77b2a881c2c92e47edaee692722c851482353ba2bfe8a14cf10364a81a664bbc423001c24b8b70d0f89791c76c51a30654be30d192e819d6ef5218d69906245565a910f40e35855771202a106aa07032bbd1b819a4c116b8d2d0c81e376c085141ab532748774cdf8eeb9934b0bcb5e19b48a8391c0cb3c5c95a634ed8aa4ae3418acb5b9cca4f7763e373682e6ff3d6b2b8a3748f82ee5defb2fc78a5636f43172f6084c87814a1f0ab728cc702081a6439ec90befffa23631e28a4506cebde82bde9bef9a3f7b2c67915c67178f2e372532bca273eceea26619cd186b8c721c0c207eada7dd6cde0eb1ef57d4f7fee6ed17806f067aa72176fba0a637dc5a2c898a6113f9804bef90dae1b710b35131c471b28db77f523047d8432caab7b40c724933c9ebe0a15c9bebc431d67c49c100d4c4cc5d4becb3e42b6597f299cfc657e2a5fcb6fab3ad6faec6c44198c4a475817"
            ).unwrap()
        )
}

pub fn word_to_hex(word: (u32, u32)) -> String {
    hex::encode(&words_to_bytes_be(&[word]))
}

pub fn words_to_bytes_be(words: &[(u32, u32)]) -> Vec<u8> {
    // Convert each u32 word to its bytes representation in big-endian order
    let mut bytes = Vec::with_capacity(words.len() * 8);
    for word in words {
        bytes.extend_from_slice(&word.0.to_be_bytes());
        bytes.extend_from_slice(&word.1.to_be_bytes());
    }
    // Convert the Vec<u8> into a slice
    bytes
}

pub fn bytes_to_words_be(input_bytes: &[u8]) -> Vec::<(u32, u32)> {
    let words: Vec::<(u32, u32)> = input_bytes
        .chunks_exact(8) // Split the input into chunks of 4 bytes each
        .map(|chunk| {
            let array: [u8; 8] = chunk.try_into().unwrap();
            let w = u64::from_be_bytes(array); // Convert the 8-byte chunk into a u64 (big-endian)
        let n0 = w >> 32;
        let n1 = w & 0xffffffff;
        (n0 as u32, n1 as u32)
        })
    .collect();
    words
}

pub fn right_rotate(n: (u32, u32), bits: usize) -> (u32, u32) {
    // return (n >> bits) | (n << (64 - bits)) & 0xFFFFFFFFFFFFFFFF
    // Ensure bits is within 0 to 63
    let bits = bits % 64;

    // Split the rotation into two parts
    if bits < 32 {
        // Rotate within and across the 32-bit boundaries
        let high = (n.0 >> bits) | (n.1 << (32 - bits));
        let low = (n.1 >> bits) | (n.0 << (32 - bits));
        (high, low)
    } else {
        // When rotating by 32 or more bits, effectively swap high and low parts
        let bits = bits - 32;
        let high = (n.1 >> bits) | (n.0 << (32 - bits));
        let low = (n.0 >> bits) | (n.1 << (32 - bits));
        (high, low)
    }
}

pub fn not(a: (u32, u32)) -> (u32, u32) {
    (!a.0, !a.1)
}

pub fn xor(a: (u32, u32), b: (u32, u32)) -> (u32, u32) {
    (a.0 ^ b.0, a.1 ^ b.1)
}

pub fn and(a: (u32, u32), b: (u32, u32)) -> (u32, u32) {
    (a.0 & b.0, a.1 & b.1)
}

pub fn shr(a: (u32, u32), num_bits: usize) -> (u32, u32) {
    assert!(num_bits < 32);
    let n0 = a.0;
    let n1 = a.1;

    if num_bits == 0 {
        return (n0, n1);
    } 

    let new_high = n0 >> num_bits;
    let carry_bits = (n0 & 0x7f) << (32 - num_bits);
    let new_low = (n1 >> num_bits) | carry_bits;

    (new_high, new_low)
}

pub fn add(a: (u32, u32), b: (u32, u32)) -> (u32, u32) {
    let sum1 = a.1.wrapping_add(b.1);
    let c = (sum1 < a.1) as u32;
    let sum0 = a.0.wrapping_add(b.0).wrapping_add(c);

    (sum0, sum1)
}

#[cfg(test)]
pub mod tests {
    use rand::RngCore;
    use rand_chacha::ChaCha8Rng;
    use rand_chacha::rand_core::SeedableRng;
    use crate::sha512::sha512_96;
    use sha2::Digest;

    #[test]
    pub fn test_compute_challenge() {
        let mut rng = ChaCha8Rng::seed_from_u64(1 as u64);

        for _ in 0..10000 {
            let mut input = [0u8; 96];
            rng.fill_bytes(&mut input);

            let challenge = sha512_96(input.as_slice().try_into().unwrap());

            let mut hasher = sha2::Sha512::new();
            hasher.update(input);
            let expected = hasher.finalize();
            assert_eq!(challenge, expected.as_slice());
        }
    }
}

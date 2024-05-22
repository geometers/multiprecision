use num_bigint::BigUint;
pub fn calc_num_limbs(log_limb_size: u32, p_bitwidth: usize) -> usize {
    let l = log_limb_size as usize;
    let mut num_limbs = p_bitwidth / l;
    while num_limbs * l <= p_bitwidth {
        num_limbs += 1;
    }

    if p_bitwidth == 256 && log_limb_size == 15 {
        return 19;
    }

    // TODO: account for cases like (15, 377) where num_limbs should be 27?
    
    num_limbs
}

pub fn calc_bitwidth(p: &BigUint) -> usize {
    if *p == BigUint::from(0u32) {
        return 0;
    }

    p.to_radix_le(2).len()
}

pub fn bytes_to_u32s_be(input_bytes: &[u8]) -> Vec::<u32> {
    let mut padded = input_bytes.to_vec();
    while padded.len() % 4 > 0 {
        padded.insert(0, 08);
    }

    let words: Vec::<u32> = padded
        .chunks_exact(4) // Split the input into chunks of 4 bytes each
        .map(|chunk| {
            let array: [u8; 4] = chunk.try_into().unwrap();
            let w = u32::from_be_bytes(array); // Convert the 4-byte chunk into a u32 (big-endian)
        w
        })
    .collect();
    words
}

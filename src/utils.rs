use ark_std::log2;

pub fn is_pow_2(x: usize) -> bool {
    (x & (x - 1)) == 0
}

pub fn next_pow2(n: usize) -> usize {
    let two: u32 = 2;
    let a: u32 = log2(n);

    if two.pow(a - 1) == n as u32 {
        return n;
    }

    two.pow(a).try_into().unwrap()
}

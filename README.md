# `multiprecision`

TODO:
- rewrite readme
- implement CIOS for 16-bit limbs

All operations are in little-endian form (where the digit in memory at the smallest
memory address is the least signficant digit).

Implementations of cryptographic protocols that rely on large integer values
(i.e. beyond 32 or 64 bits) must represent them using
multiprecision-arithmetic. Specifically, such *big integers* (bigints) are
represented as an array of $n$-bit *limbs* or digits.

The `multiprecision` Rust library implements big integer and finite field
arithmetic algorithms. The key difference between this library and others (such
as [`num_bigint`](https://crates.io/crates/num-bigint)) is that this library
internally represents the limbs of bigints as arrays of limbs whose size is
defined by the programmer, rather than some default. The purpose of doing so,
despite poorer performance, is to offer reference code for developers who need
to build GPU shaders which handle bigint arithmetic.

It is necessary that the limb size be programmer-defined because smaller limb
sizes, coupled with an iterative algorithm, allows for more efficient
Montgomery multiplications, as smaller limb sizes eliminates some carry
operations, if not all. Please refer to [Gregor Mitscha-Baude's `montgomery`
repository](https://github.com/mitschabaude/montgomery) for a detailed
description of this algorithm.

Since most GPUs are limited to 32-bit unsigned integers, we only implement
algorithms that support limb sizes of 12 to 16 bits, inclusive.

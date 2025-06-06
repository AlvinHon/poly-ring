[![version]][crates.io] [![workflow status]][workflow] [![codecov status]][codecov]

[version]: https://img.shields.io/crates/v/poly-ring-xnp1.svg
[crates.io]: https://crates.io/crates/poly-ring-xnp1
[workflow status]: https://github.com/AlvinHon/poly-ring/actions/workflows/build_and_test.yml/badge.svg?branch=main
[workflow]: https://github.com/AlvinHon/poly-ring/actions/workflows/build_and_test.yml
[codecov status]: https://codecov.io/gh/AlvinHon/poly-ring/graph/badge.svg?token=6TI83EGP30
[codecov]: https://codecov.io/gh/AlvinHon/poly-ring

# Polynomial Ring Z\[X\]/(X^n + 1)

```math
Z[X]/(X^n + 1)
```

This library provides arithmetic operations over a specific polynomial ring `Z[X]/(X^n + 1)` implemented in a compact and efficient manner. I.e. the ring of polynomials over `Z` of degree at most `n-1` for `n` some power of two. This ring is commonly used in lattice based cryptosystems.

Polynomial additions and multiplications are implemented with implicit polynomial modulo operations, i.e. the modulus is "invisible" when you perform the methods in the trait`std::ops::Add` and `std::ops::Mul`. 

```rust
use poly_ring_xnp1::Polynomial;

const N: usize = 4; // power of two
// p(x) = 1 + 2x + 3x^2 + 4x^3
let p = Polynomial::<i32, N>::new(vec![1, 2, 3, 4]);
// q(x) = x
let q = Polynomial::<i32, N>::new(vec![0, 1]);
// a(x) = (1 + 2x + 3x^2 + 4x^3) * x mod (x^4 + 1)
let a = p * q;
assert_eq!(a, Polynomial::<i32, N>::new(vec![-4, 1, 2, 3]));
```
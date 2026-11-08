module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v67f76fdbbe1d.CookMagyar.Local
public import Mathlib.RingTheory.Nilpotent.Basic
@[expose] public section
namespace SystolicGrowth
namespace CookMagyarLocal
/-! # Unit solutions at the primes two and three

The local argument for `x ^ 3 - x` at the exceptional primes can be made
completely explicit.  Two elementary identities are the point:

* `f(2y + 1) + f(2y - 1) = 8 (y + 2y ^ 3)`;
* `f(1 + 3y) = 3 (2y + 9y ^ 2 + 9y ^ 3)`.

The two parameter maps on the right are permutations modulo every power of
`2` and `3`, respectively.  Thus every target divisible by `8` has a
two-variable unit solution modulo `2 ^ k`, and every target divisible by `3`
has a one-variable unit solution modulo `3 ^ k`.  In particular these apply
to the targets divisible by `24` in the Cook--Magyar application.

The proof works uniformly in the exponent; no finite computation or
unformalized lifting lemma is used.
-/
end CookMagyarLocal
end SystolicGrowth

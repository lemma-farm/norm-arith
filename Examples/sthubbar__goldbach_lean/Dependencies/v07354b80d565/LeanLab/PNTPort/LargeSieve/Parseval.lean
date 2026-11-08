module
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.PNTPort.LargeSieve.Farey
/-!
# Parseval modulo q and the large sieve over primes

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

* `sum_e_mul_div`: `∑_{c<q} e(kc/q)` is `q` if `q ∣ k` and `0` otherwise.
* `parseval_mod`: `∑_{c<q} ‖S(c/q)‖² = q ∑_{b<q} ‖Z(q,b)‖²`, where `Z(q,b)` sums `a_n` over
  `n ≡ b mod q`.
* `prime_large_sieve`: `∑_{p≤Q prime} (p ∑_b ‖Z(p,b)‖² - ‖Z‖²) ≤ (N + 2Q²) ∑ ‖a_n‖²`, the
  prime modulus form of the arithmetic large sieve, Renyi and Gallagher.
-/
@[expose] public section
namespace LeanLab.PNTPort.LargeSieve
open Complex Finset Real
end LeanLab.PNTPort.LargeSieve

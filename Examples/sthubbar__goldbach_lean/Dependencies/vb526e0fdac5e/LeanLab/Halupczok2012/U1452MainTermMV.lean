module
public import Examples.sthubbar__goldbach_lean.Dependencies.vb526e0fdac5e.LeanLab.Halupczok2012.U1439Thm2Reduction
/-!
# P0077 Halupczok 2012, the main term step: the CRT combination, unit U-1452

AI wrote the Lean code, Claude, run 20261022T0003Z-15508. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

The paper's main term step, the displays after (10) in the proof of Theorem 2, expands
`𝔖(n - p₁)` as a finite sum over squarefree `s ≤ L^C` of functions of `p₁ mod s`, combines
`p₁ ≡ a (q)` with `p₁ ≡ b (s)` by the Chinese remainder theorem into one class mod `[q, s]`, and
applies Theorem 3 of Perelli-Pintz-Salerno at the moduli `[q, s]`. This file proves that
combination step for ONE modulus `s` and ANY `s`-periodic weight `f`, uniformly in `s`:

* `modEq_and_iff_lcm`: `p ≡ a (q) ∧ p ≡ b (s) ↔ p ≡ x ([q, s])` for any common solution `x`. PROVED.
* `crt_exists_iff`: a common solution exists iff `(q, s) ∣ a - b`. PROVED.
* `class_sum_eq_theta`: the primes of `P1` in the class `b mod s` are those of one class mod
  `[q, s]`, a class coprime to `[q, s]`. PROVED.
* `perQ_eq`: for one `q`, `∑_{p ≡ a (q)} log p f(p) - Y/φ([q,s]) ∑_{b ∈ G} f(b)` equals
  `∑_{b ∈ G} f(b) (θ(X, Y; [q, s], x_b) - Y/φ([q, s]))`, `G` the reduced `b mod s` compatible
  with `a mod q`. PROVED.
* `crtStep`: CONDITIONAL ON `Theorem3` only:
  `∑_{q ≤ Q, (a,q)=1} |∑_{p ≡ a (q)} log p f(p) - Y/φ([q,s]) ∑_{b ∈ G} f(b)| ≤ s² M C Y L^{-A}`
  whenever `Q s ≪ Y X^{-1/2} (log X)^{-B}`, `|f| ≤ M`, `s ≤ X`.

NOT done here: the Ramanujan expansion of `𝔖`, the tail `s > L^C`, and the Euler product
identification with `𝔗`. So `MainTermMV` is still NOT derived from `Theorem3`.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset
/-! ### The Chinese remainder theorem for two moduli -/
end LeanLab.Halupczok2012

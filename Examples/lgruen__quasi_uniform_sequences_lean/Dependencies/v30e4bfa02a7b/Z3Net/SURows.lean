module
public import Mathlib
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.SUNet
set_option autoImplicit false
@[expose] public section
/-!
# Entry U, part 5: the first offset row is the design, for every `k` (hypothesis (H1))

* `propN`: Lemma R_s / Proposition N_s in the `E`-basis: `Q_c^(-k) Ψ_cd[0, j] = w_cd y_cd^(k-1-j)`,
  proved by evaluating the cofactor of `(t - a_c)^k` in `E_{d,j}` at `a_c` (finite `c`) resp. by
  the degree of `E_{d,j}` (`c = ∞`).
* `propG`: `w y^n = ∑_{i<s-1} γ_{n,i} w y^i` at every node `y = y_cd` (the remainder of `X^n`
  modulo `∏_{c ≠ d} (X - y_cd)`, computed by `rootsPoly`/`xpowRem`).
* `design_eq`: the design entries are `λ'_c ∑_{n' ≤ n} w y^(n') U'_d[n', n]` (Proposition F; the
  `∞` column via the falling factorial `∑ stir n i a^i = a(a-1)⋯(a-n+1)`).
* `row0`: `Φ'_cd[0, j] = F_{k-1-j}[c][d]` for all `c, d`, `k ≥ 1`.
-/
namespace Z3NetU.Proofs
open Polynomial Finset Matrix Z3NetU
noncomputable section
variable {R : Type*} [CommRing R] {iv : ℕ → R}
/-! ## Proposition N_s -/
end
end Z3NetU.Proofs

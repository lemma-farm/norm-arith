module
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FEbasis
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Entry F, part 8: `lem:Rs` (generating functions of row 0 of `Φ^F`)

Row `0` of `Φ^F_cd · Toep(uN_d)` is `Q_c^k w_cd y_cd^n` at the `x`-index `n` (`key_Psi`,
`off_Evec`); multiplying its generating function by the linear factor `den'` (`1`, `1 - a_c x`,
`a_c - a_d - x`) telescopes to `Q_c^k` modulo `x^k`, and `uN_d den'` is a unit power series.
-/
namespace Z3NetF.Proofs
open Polynomial Finset Matrix
noncomputable section
variable {R : Type*} [CommRing R]
variable {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)
end
end Z3NetF.Proofs

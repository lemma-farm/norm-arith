module
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FTs
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Entry F, part 15: `lem:Tsplit` (box minors of the split frame)

The split box matrix is literally the Hermite matrix of the `2s` points `v_0, u_0, v_1, u_1, …`
with multiplicities `min(d_c, k)`, `(d_c - k)_+` (the row blocks line up because the prefix sums
agree, `pre_split2`); the converse of the net criterion uses the boxes `(k, …, k)`, one coordinate
`k+1` and one `k-1`, and two `k+1`, two `k-1` (`s ≥ 4`).
-/
namespace Z3NetF.Proofs
open Polynomial Finset Matrix
noncomputable section
variable {R : Type*} [CommRing R] {s : ℕ}
end
end Z3NetF.Proofs

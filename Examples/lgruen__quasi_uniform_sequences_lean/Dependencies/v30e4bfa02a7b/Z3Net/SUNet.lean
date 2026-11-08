module
public import Mathlib
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.SUDefs
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.SUPoly
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.SUGraph
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.NetBasic
set_option autoImplicit false
@[expose] public section
/-!
# Entry U, part 3: units and `t = 0` (Theorem U(1))

* `IvOK iv n`: `iv i` is an inverse of `i` for `1 ≤ i ≤ n` (`n = s - 2`). Then `ivz`, `Q_c^(-k)`,
  `1/n!`, `L_s` and the row scalings are units.
* The net is the frame read through lower-triangular scrambles: with the coefficients
  `m_d = U'^(k)_d n_d` of the cell vector `n` in the basis `E_{d,j}`, `V = ∑ m_{d,j} E_{d,j}` has
  cells `U0_c m_c` (`U0_c` lower triangular with unit diagonal) and the final offset digit `k + r`
  of coordinate `c` is `(own terms in n_c) + s_{c,r} · (digit k + r of reading c of V)` with a unit
  `s_{c,r}`. Hence vanishing first digits of the net force vanishing first digits of every reading
  of `V`, Lemma T_s gives `V = 0`, and `n = 0` (`box_kernel`).
-/
namespace Z3NetU.Proofs
open Polynomial Finset Matrix Z3NetU
noncomputable section
variable {R : Type*} [CommRing R]
/-! ## Lower-triangular matrices (copied from the 4D entry) -/
variable {iv : ℕ → R} {n : ℕ}
section kernel
variable (iv)
end kernel
end
end Z3NetU.Proofs

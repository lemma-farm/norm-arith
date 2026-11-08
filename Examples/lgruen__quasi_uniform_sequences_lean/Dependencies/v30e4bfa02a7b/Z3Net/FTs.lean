module
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FHermite
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FBox
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Entry F, part 5: `lem:hermite` (as stated) and the net criterion of `lem:Ts`

* `hermite_det_core`: the Hermite matrix of `n` points and an `∞`-jet is the frame box matrix with
  `∞` at the last coordinate; the product is re-indexed.
* `hermite_ne_zero_core`, `hermite_rows_core`: the two consequences.
* `frame_net_iff_core`: for rational places (reduced modulo `q`) and `m ≥ 2`: the frame is a
  `(0,m,s)`-net over `ℤ/qℤ` iff the finite places are distinct modulo every prime factor of `q`
  (`lem:nie` plus the exact minors; for the converse, the box with `d_c = m - 1`, `d_c' = 1`).
-/
namespace Z3NetF.Proofs
open Polynomial Finset Matrix
noncomputable section
section hermite
variable {R : Type*} [CommRing R] {n m : ℕ}
/-- The places of the Hermite matrix as a frame (`∞` last). -/
def hx (x : Fin n → R) : Fin (n + 1) → R := fun P => if h : (P : ℕ) < n then x ⟨P, h⟩ else 0
end hermite
/-! ## The net criterion of `lem:Ts` -/
end
end Z3NetF.Proofs

module
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FRs
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Entry F, part 9: `prop:Gs` (the all-`k` gauge)
-/
namespace Z3NetF.Proofs
open Polynomial Finset Matrix
noncomputable section
variable {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)
  (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R)
/-! ## The gauge is lower triangular with unit diagonal -/
end
end Z3NetF.Proofs

module
public import Mathlib
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.SUDefs
set_option autoImplicit false
@[expose] public section
/-!
# Entry U, part 2: graph-form bookkeeping (`s` coordinates)

Index digit `ix k d l = d k + l` is level `l` of the cell of axis `d`; digit `i < k` of coordinate
`c` of a graph-form net is the index digit `ix k c i`, digit `k + r` is
`∑_{d,l} Φ_cd[r,l] n_{d,l}`.
-/
namespace Z3NetU.Proofs
open Finset Matrix Z3NetU
lemma idx_lt {s : ℕ} (k : ℕ) (d : Fin s) (l : Fin k) : (d : ℕ) * k + l < s * k := by
  have := d.isLt; have := l.isLt
  calc (d : ℕ) * k + l < (d : ℕ) * k + k := by omega
    _ = ((d : ℕ) + 1) * k := by ring
    _ ≤ s * k := Nat.mul_le_mul_right _ (by omega)
/-- The index digit `n_{d k + l}` (level `l` of the cell of axis `d`). -/
def ix {s : ℕ} (k : ℕ) (d : Fin s) (l : Fin k) : Fin (s * k) := ⟨(d : ℕ) * k + l, idx_lt k d l⟩
variable {R : Type*} [CommRing R]
end Z3NetU.Proofs

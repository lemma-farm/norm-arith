module
public import Mathlib
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FDefs
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.NetBasic
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.SUFrame
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.SUBoxMinor
set_option autoImplicit false
@[expose] public section
/-!
# Entry F, part 1: bridges and the row structure of box matrices

* `boxLoc_eq`, `boxMatrix_eq`: the entry-F copies agree with entry U's definitions.
* `pre d c = d_0 + … + d_{c-1}` (entry U's `Z3NetU.Proofs.pre`); row `pre d c + i` of the box
  matrix is row `i` of `C c` (`box_row_pre`), and every row is of this form (`box_row_cover`).
* `box_mul_right`, `box_map`: right multiplication and ring homomorphisms commute with taking box
  matrices.
* `digSum_div_prefix`: the quotient of a base-`q` digit sum by `q^(m-d)` is the digit sum of the
  first `d` digits.
-/
namespace Z3NetF.Proofs
open Matrix Finset
noncomputable section
abbrev pre {s : ℕ} (d : Fin s → ℕ) (c : ℕ) : ℕ := Z3NetU.Proofs.pre d c
lemma digSum_div_prefix (q : ℕ) (hq : 0 < q) : ∀ (m : ℕ) (f : Fin m → ℕ), (∀ j, f j < q) →
    ∀ d (hd : d ≤ m), Z3Net.Proofs.digSum q m f / q ^ (m - d) =
      Z3Net.Proofs.digSum q d (fun j => f ⟨j, lt_of_lt_of_le j.isLt hd⟩) := by
  intro m
  induction m with
  | zero =>
    intro f _ d hd
    obtain rfl : d = 0 := by omega
    simp [Z3Net.Proofs.digSum]
  | succ m ih =>
    intro f hf d hd
    by_cases hdm : d = m + 1
    · subst hdm
      simp only [Nat.sub_self, pow_zero, Nat.div_one]
    · have hd' : d ≤ m := by omega
      rw [Z3Net.Proofs.digSum_succ]
      have hr := hf (Fin.last m)
      rw [show m + 1 - d = (m - d) + 1 by omega, pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.mul_add_div hq, Nat.div_eq_of_lt hr, add_zero]
      rw [ih (fun j => f j.castSucc) (fun j => hf _) d hd']
      rfl
end
end Z3NetF.Proofs

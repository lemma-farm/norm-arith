/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Mathlib
public import Mathlib.Data.Fin.Rev
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Collision diagrams are finite words of unordered particle pairs with no equal adjacent entries, as in Tsai’s equation (2.11). -/
@[expose] public section
namespace Critical2DKPZ.DeltaBose
/-- An unordered pair of distinct particle labels, represented in increasing order. -/
abbrev CollisionPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
/-- A fixed-length collision word with no adjacent repetition. -/
abbrev CollisionWord (n m : ℕ) :=
  {w : Fin m → CollisionPair n // ∀ i j : Fin m, i.val + 1 = j.val → w i ≠ w j}
/-- There are no collision pairs for fewer than two particles. -/
theorem collisionPair_impossible {n : ℕ} (hn : n ≤ 1) (α : CollisionPair n) : False := by
  have hlt := α.2
  have hi := α.1.1.isLt
  have hj := α.1.2.isLt
  omega
/-- A single particle has no nonempty collision diagram. -/
instance collisionWord_one_isEmpty (m : ℕ) : IsEmpty (CollisionWord 1 (m + 1)) :=
  ⟨fun w => collisionPair_impossible le_rfl (w.1 0)⟩
/-- The only possible collision pair of two particles. -/
def pairTwo : CollisionPair 2 := ⟨(0, 1), by decide⟩
instance collisionPair_two_subsingleton : Subsingleton (CollisionPair 2) := by
  refine ⟨fun a b => ?_⟩
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals
    have ha := a.2
    have hb := b.2
    have hai := a.1.1.isLt
    have haj := a.1.2.isLt
    have hbi := b.1.1.isLt
    have hbj := b.1.2.isLt
    omega
instance collisionWord_two_succ_succ_isEmpty (m : ℕ) : IsEmpty (CollisionWord 2 (m + 2)) := by
  refine ⟨fun w => ?_⟩
  have h := w.2 ⟨0, by omega⟩ ⟨1, by omega⟩ (by rfl)
  exact h (Subsingleton.elim _ _)
end Critical2DKPZ.DeltaBose

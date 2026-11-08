-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.WeakDeriv
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}
theorem exists_test_plateau (Ω : Opens (Fin n → ℝ)) (K : Compacts (Fin n → ℝ))
    (hK : (K : Set (Fin n → ℝ)) ⊆ Ω) :
    ∃ (χ : TestFunction Ω ℝ (⊤ : ℕ∞)) (U : Set (Fin n → ℝ)),
      IsOpen U ∧ (K : Set (Fin n → ℝ)) ⊆ U ∧ U ⊆ Ω ∧ EqOn χ 1 U := by
  obtain ⟨W, hW, hKW, hclW, hcW⟩ :=
    exists_open_between_and_isCompact_closure K.isCompact Ω.isOpen hK
  obtain ⟨U, hU, hKU, hclU, _⟩ :=
    exists_open_between_and_isCompact_closure K.isCompact hW hKW
  obtain ⟨χ, hχ, _, hs, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW isClosed_closure hclU
  have ht : tsupport χ ⊆ Ω := by rw [tsupport, hs]; exact hclW
  let ψ : TestFunction Ω ℝ (⊤ : ℕ∞) :=
    ⟨χ, hχ, by simpa [HasCompactSupport, tsupport, hs] using hcW, ht⟩
  refine ⟨ψ, U, hU, hKU, subset_closure.trans (hclU.trans (subset_closure.trans hclW)), ?_⟩
  intro x hx
  exact (hone x).mp (subset_closure hx)
end RothschildStein.S

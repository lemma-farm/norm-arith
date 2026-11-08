/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.GeneratorScaling.Algebra
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# `L¹` bounds for rescaled test functions and their generators

The closed unit parabolic ball has volume at most `16` (it lies in `[-1,1]⁴`), so every
`φ ∈ B^r` has `∫ |φ| ≤ 16`, and for `φ ∈ B^4`, `∫ |L φ| ≤ 16 (…)`. We package the hypotheses
of `RegularisingSemigroup.abs_pairing_le` for `φ^c_z` and `L φ^c_z`.
-/
public section
namespace RegularityStructures
open MeasureTheory
/-- The closed parabolic ball of radius `c` about `z`. -/
def closedParabolicBall (z : ParabolicSpace) (c : ℝ) : Set ParabolicSpace :=
  {w | parabolicNorm (w - z) ≤ c}
theorem isClosed_closedParabolicBall (z : ParabolicSpace) (c : ℝ) :
    IsClosed (closedParabolicBall z c) :=
  isClosed_le (continuous_parabolicNorm.comp (continuous_id.sub continuous_const)) continuous_const
theorem abs_fst_le_one {w : ParabolicSpace} (h : parabolicNorm w ≤ 1) : |w.1| ≤ 1 := by
  have h1 : Real.sqrt |w.1| ≤ 1 := by
    have : 0 ≤ ∑ i, |w.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    unfold parabolicNorm at h
    linarith
  rw [Real.sqrt_le_left (by norm_num)] at h1
  linarith
theorem abs_snd_le_one {w : ParabolicSpace} (h : parabolicNorm w ≤ 1) (i : Fin 3) :
    |w.2 i| ≤ 1 := by
  have h1 : |w.2 i| ≤ ∑ j, |w.2 j| :=
    Finset.single_le_sum (f := fun j => |w.2 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have := Real.sqrt_nonneg |w.1|
  unfold parabolicNorm at h
  linarith
theorem closedParabolicBall_zero_one_subset :
    closedParabolicBall 0 1 ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.pi Set.univ fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1 := by
  intro w hw
  have hw' : parabolicNorm w ≤ 1 := by simpa [closedParabolicBall] using hw
  refine ⟨abs_le.1 (abs_fst_le_one hw'), fun i _ => abs_le.1 (abs_snd_le_one hw' i)⟩
theorem isCompact_closedParabolicBall (z : ParabolicSpace) {c : ℝ} (hc : 0 < c) :
    IsCompact (closedParabolicBall z c) := by
  have hK : IsCompact (closedParabolicBall 0 1) :=
    (isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)).of_isClosed_subset
      (isClosed_closedParabolicBall 0 1) closedParabolicBall_zero_one_subset
  have himg : closedParabolicBall z c =
      (fun u => parabolicDilate c u + z) '' closedParabolicBall 0 1 := by
    ext w
    constructor
    · intro hw
      refine ⟨parabolicDilate c⁻¹ (w - z), ?_, ?_⟩
      · simp only [closedParabolicBall, Set.mem_ofPred_eq, sub_zero]
        rw [parabolicNorm_parabolicDilate_inv hc, inv_mul_le_iff₀ hc]
        simpa [closedParabolicBall] using hw
      · simp [parabolicDilate_parabolicDilate_inv hc.ne']
    · rintro ⟨u, hu, rfl⟩
      simp only [closedParabolicBall, Set.mem_ofPred_eq, sub_zero] at hu ⊢
      rw [add_sub_cancel_right, parabolicNorm_parabolicDilate hc.le]
      nlinarith
  rw [himg]
  refine hK.image ?_
  unfold parabolicDilate
  fun_prop
theorem hasCompactSupport_of_eq_zero {f : ParabolicSpace → ℝ} {c : ℝ} (hc : 0 < c)
    (z : ParabolicSpace) (hf : ∀ w, c < parabolicNorm (w - z) → f w = 0) : HasCompactSupport f := by
  refine (isCompact_closedParabolicBall z hc).of_isClosed_subset isClosed_closure
    (closure_minimal ?_ (isClosed_closedParabolicBall z c))
  intro w hw
  by_contra h
  exact hw (hf w (not_le.1 h))
theorem hasCompactSupport_of_eq_zero_unit {f : ParabolicSpace → ℝ}
    (hf : ∀ w, 1 < parabolicNorm w → f w = 0) : HasCompactSupport f :=
  hasCompactSupport_of_eq_zero one_pos 0 (by simpa using hf)
theorem integrable_of_continuous_unit {f : ParabolicSpace → ℝ} (hc : Continuous f)
    (hf : ∀ w, 1 < parabolicNorm w → f w = 0) : Integrable f :=
  hc.integrable_of_hasCompactSupport (hasCompactSupport_of_eq_zero_unit hf)
end RegularityStructures
end

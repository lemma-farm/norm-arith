/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.SemigroupTestTreesI3PsiPrincipal
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3Psi2DiagramMultiWeighted
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The weighted principal diagram of the difference of `I(Ψ³)Ψ²`, for arbitrary `z, z'`

Without Hölder gains the weight `|δK(z, w)| |δK(z', v)| s(w - v)^(-(3+τ))` is dominated by
`B² 1_{|w.1| ≤ |z.1|+1} (s₃(z;w) + s₃(0;w)) (s₃(z';v) + s₃(0;v)) s_{3+τ}(w;v)`, a two-level majorant
with bound `C (1 + |z.1|)` (`i3Psi2PrincipalWeighted_twoLevelLe_global`).
-/
public section
open MeasureTheory Set
namespace RegularityStructures
/-- **Two-level bound for the plain principal majorant on a slab.** -/
theorem twoLevelLe_principalPlain {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ}, 0 ≤ T → ∀ z z' : SpaceTime,
      TwoLevelLe (fun w v => Set.indicator {w : SpaceTime | |w.1| ≤ T}
          (fun w => singularPow 3 z w + singularPow 3 0 w) w *
        ((singularPow 3 z' v + singularPow 3 0 v) * singularPow (3 + τ) w v))
        (C * (1 + T)) := by
  obtain ⟨C1, hC1, h1⟩ := singularIntLe_mul_two (a := 3) (b := 3 + τ) (η := 1 + τ) (by norm_num)
    (by norm_num) (by linarith) (by linarith) (by linarith) (by ring)
  refine ⟨8 * C1 * 160, by positivity, ?_⟩
  intro T hT z z'
  set S : Set SpaceTime := {w : SpaceTime | |w.1| ≤ T} with hS
  set m : SpaceTime → ℝ := Set.indicator S (fun w => singularPow 3 z w + singularPow 3 0 w)
    with hm
  have hm0 : ∀ w, 0 ≤ m w := fun w => Set.indicator_nonneg (fun w _ =>
    add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) w
  have hmm : Measurable m := (((measurable_singularPow 3 z).add (measurable_singularPow 3 0))
    ).indicator (measurableSet_abs_fst_le T)
  have sl : ∀ c : SpaceTime, SingularIntLe (Set.indicator S (singularPow (4 + τ) c))
      (80 / (5 - (4 + τ)) + 2 * T) := fun c => singularIntLe_slab_singularPow (by linarith)
    (by linarith) hT c
  have hsum : SingularIntLe (fun w => 2 * Set.indicator S (singularPow (4 + τ) z) w +
      2 * Set.indicator S (singularPow (4 + τ) z') w + 4 * Set.indicator S (singularPow (4 + τ) 0) w)
      (2 * (80 / (5 - (4 + τ)) + 2 * T) + 2 * (80 / (5 - (4 + τ)) + 2 * T) +
        4 * (80 / (5 - (4 + τ)) + 2 * T)) :=
    (((sl z).const_mul (c := 2) (by norm_num)).add ((sl z').const_mul (c := 2)
      (by norm_num))).add ((sl 0).const_mul (c := 4) (by norm_num))
  set H : SpaceTime → ℝ := fun w => m w * (C1 * (singularPow (1 + τ) z' w +
    singularPow (1 + τ) 0 w)) with hH
  have hHle : SingularIntLe H (C1 * (2 * (80 / (5 - (4 + τ)) + 2 * T) +
      2 * (80 / (5 - (4 + τ)) + 2 * T) + 4 * (80 / (5 - (4 + τ)) + 2 * T))) := by
    refine ((hsum.const_mul (c := C1) hC1)).of_le ?_ ?_ ?_
    · exact ((hmm.mul (measurable_const.mul
        ((measurable_singularPow (1 + τ) z').add (measurable_singularPow (1 + τ) 0))))
        ).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun w => mul_nonneg (hm0 w)
        (mul_nonneg hC1 (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)))
    · filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos z',
        ae_torusParabolicSize_sub_pos 0] with w a b c
      by_cases hw : w ∈ S
      · simp only [hH, hm, Set.indicator_of_mem hw]
        have e1 := singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) a b
        have e2 := singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) a c
        have e3 := singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) c b
        have e4 := singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) c c
        have e : (3 : ℝ) + (1 + τ) = 4 + τ := by ring
        rw [e] at e1 e2 e3 e4
        have : (singularPow 3 z w + singularPow 3 0 w) *
            (singularPow (1 + τ) z' w + singularPow (1 + τ) 0 w) ≤
            2 * singularPow (4 + τ) z w + 2 * singularPow (4 + τ) z' w +
              4 * singularPow (4 + τ) 0 w := by
          calc _ = singularPow 3 z w * singularPow (1 + τ) z' w +
                singularPow 3 z w * singularPow (1 + τ) 0 w +
                singularPow 3 0 w * singularPow (1 + τ) z' w +
                singularPow 3 0 w * singularPow (1 + τ) 0 w := by ring
            _ ≤ _ := by linarith
        calc (singularPow 3 z w + singularPow 3 0 w) *
            (C1 * (singularPow (1 + τ) z' w + singularPow (1 + τ) 0 w))
            = C1 * ((singularPow 3 z w + singularPow 3 0 w) *
              (singularPow (1 + τ) z' w + singularPow (1 + τ) 0 w)) := by ring
          _ ≤ C1 * (2 * singularPow (4 + τ) z w + 2 * singularPow (4 + τ) z' w +
              4 * singularPow (4 + τ) 0 w) := mul_le_mul_of_nonneg_left this hC1
      · simp [hH, hm, hw]
  have hint : ∀ p q : SpaceTime, 0 < torusParabolicSize (p - q) → SingularIntLe
      (fun v => singularPow 3 p v * singularPow (3 + τ) q v)
      (C1 * singularPow (1 + τ) p q) := fun p q hpq => by
    simpa [singularPow] using h1 p q hpq
  refine ⟨?_, H, ?_, ?_⟩
  · filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    have i1 := (hint z' w a).1
    have i2 := (hint 0 w b).1
    exact ((i1.add i2).congr (Filter.Eventually.of_forall fun v => by
      simp only [Pi.add_apply]; ring)).const_mul (m w)
  · refine hHle.mono_right ?_
    have hτ' : 80 / (5 - (4 + τ)) ≤ 160 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hC : 0 ≤ C1 := hC1
    nlinarith
  · filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    have j1 := hint z' w a
    have j2 := hint 0 w b
    have hs := j1.add j2
    rw [integral_const_mul]
    have := hs.2
    simp only at this
    rw [show (∫ v, (singularPow 3 z' v + singularPow 3 0 v) * singularPow (3 + τ) w v) =
      ∫ v, (singularPow 3 z' v * singularPow (3 + τ) w v +
        singularPow 3 0 v * singularPow (3 + τ) w v) from
        integral_congr_ae (Filter.Eventually.of_forall fun v => by ring)]
    refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) (hm0 w)
    simp only [singularPow, zero_sub]
    ring_nf
end RegularityStructures
end

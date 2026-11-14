module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_3e9aed99fc3df215aed6_FiniteDifference ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite differences of scalar functions

Generic estimates used in Lemma 4.2 of the four-results note.
-/
public section
namespace Critical2DKPZ.Extensions.Response


set_option linter.unusedVariables false in
/-- Error of the second forward difference for a jet with Lipschitz second component. -/
theorem second_diff_quotient_error_le (f f₁ f₂ : ℝ → ℝ) (x ε B : ℝ)
    (hε : 0 < ε) (hf : ∀ y, HasDerivAt f (f₁ y) y)
    (hf₁ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (hLip : ∀ y ∈ Set.Icc x (x + 2 * ε), |f₂ y - f₂ x| ≤ B * |y - x|) 
    (h_Critical2DKPZ_Extensions_Response_second_difference_le_of_second_deriv_le : ∀ (f f₁ f₂ : ℝ → ℝ) (x ε c B : ℝ),
      0 < ε →
        (∀ (y : ℝ), HasDerivAt f (f₁ y) y) →
          (∀ (y : ℝ), HasDerivAt f₁ (f₂ y) y) →
            (∀ y ∈ Set.Icc x (x + 2 * ε), f₂ y ≤ c + B * (y - x)) →
              f (x + 2 * ε) - 2 * f (x + ε) + f x ≤ c * ε ^ 2 + B * ε ^ 3)
    :
    |(f (x + 2 * ε) - 2 * f (x + ε) + f x) / ε ^ 2 - f₂ x| ≤ B * ε := by
  have hu := h_Critical2DKPZ_Extensions_Response_second_difference_le_of_second_deriv_le f f₁ f₂ x ε (f₂ x) B hε hf hf₁
    (fun y hy => by
      have h := (abs_le.mp (hLip y hy)).2
      rw [abs_of_nonneg (sub_nonneg.mpr hy.1)] at h
      linarith only [h])
  have hl := h_Critical2DKPZ_Extensions_Response_second_difference_le_of_second_deriv_le (fun y => -f y)
    (fun y => -f₁ y) (fun y => -f₂ y) x ε (-f₂ x) B hε
    (fun y => (hf y).neg) (fun y => (hf₁ y).neg)
    (fun y hy => by
      have h := (abs_le.mp (hLip y hy)).1
      rw [abs_of_nonneg (sub_nonneg.mpr hy.1)] at h
      linarith only [h])
  have heq : (f (x + 2 * ε) - 2 * f (x + ε) + f x) / ε ^ 2 - f₂ x =
      (f (x + 2 * ε) - 2 * f (x + ε) + f x - f₂ x * ε ^ 2) / ε ^ 2 := by
    field_simp
  rw [heq, abs_le]
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    nlinarith only [hl]
  · apply (div_le_iff₀ (sq_pos_of_pos hε)).2
    nlinarith only [hu]
end Critical2DKPZ.Extensions.Response

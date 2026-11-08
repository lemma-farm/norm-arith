/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.Phi43.BPHZ.TreeI2Psi2DiagramKernel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Integrals of the kernel increment against singular weights

With `A(w) = K(y - w) - K(x - w)` and `r = s(y - x)`:

* `i2Psi2LintBound_kernel_sub_two`: `∫ |A(w)| s(g - w)^(-2) dw ≲ B r^θ (s(y - g)^(-θ) + s(x - g)^(-θ))`
  for `θ ∈ (0, 1]`;
* `i2Psi2LintBound_kernel_sub_three`: `∫ |A(w)| s(g₁ - w)^(-1) s(g₂ - w)^(-κ) dw ≲
  B r^θ (s(y - g₂)^(-(θ+κ-1)) + s(x - g₂)^(-(θ+κ-1)) + 2 s(g₁ - g₂)^(-(θ+κ-1)))` for
  `θ ∈ [0, 1)` and `θ + κ > 1`;
* `i2Psi2LintBound_kernel_sub_slab`: `∫ |A(w)| s(g₁ - w)^(-λ₁) s(g₂ - w)^(-λ₂) dw ≲ B r^θ` when
  `3 + θ + λ₁ + λ₂ < 5` (no singular output), under the support hypotheses.

The constants depend only on the exponents.  [Hai14, Lemma 10.14, Lemma 10.18].
-/
public section
open MeasureTheory
namespace RegularityStructures
private theorem weight_mul_nonneg (p g : SpaceTime) (a b : ℝ) (w : SpaceTime) :
    0 ≤ torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
theorem i2Psi2LintBound_kernel_sub_slab {θ l₁ l₂ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hl₁ : 0 ≤ l₁)
    (hl₂ : 0 ≤ l₂) (he : 3 + θ + l₁ + l₂ < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      ∀ x y g₁ g₂ : SpaceTime, |y.1 - x.1| ≤ 1 → |g₁.1 - x.1| ≤ 2 → |g₂.1 - x.1| ≤ 2 →
        i2Psi2LintBound volume (fun w => |K (y - w) - K (x - w)| *
          (torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂)))
          (C * B * torusParabolicSize (y - x) ^ θ) := by
  obtain ⟨CT, hCT, hT⟩ := i2Psi2LintBound_slab_triple (l₁ := 3 + θ) (l₂ := l₁) (l₃ := l₂)
    (by linarith) hl₁ hl₂ (by linarith) (by linarith)
  refine ⟨24 * CT, by positivity, ?_⟩
  intro K B hB hKs hKb hKi x y g₁ g₂ hxy hg₁ hg₂
  have hy2 : |y.1 - x.1| ≤ 2 := by linarith
  have hx2 : |x.1 - x.1| ≤ 2 := by simp
  have ty := hT x.1 y g₁ g₂ hy2 hg₁ hg₂
  have tx := hT x.1 x g₁ g₂ hx2 hg₁ hg₂
  have m : ∀ p : SpaceTime, Measurable fun w : SpaceTime => i2Psi2Slab x.1 w *
      (torusParabolicSize (p - w) ^ (-(3 + θ)) * torusParabolicSize (g₁ - w) ^ (-l₁) *
        torusParabolicSize (g₂ - w) ^ (-l₂)) := fun p =>
    (measurable_i2Psi2Slab _).mul (((measurable_torusParabolicSize_sub_rpow p _).mul
      (measurable_torusParabolicSize_sub_rpow g₁ _)).mul
      (measurable_torusParabolicSize_sub_rpow g₂ _))
  have n : ∀ (p : SpaceTime) w, 0 ≤ i2Psi2Slab x.1 w *
      (torusParabolicSize (p - w) ^ (-(3 + θ)) * torusParabolicSize (g₁ - w) ^ (-l₁) *
        torusParabolicSize (g₂ - w) ^ (-l₂)) := fun p w =>
    mul_nonneg (i2Psi2Slab_nonneg _ _) (mul_nonneg (mul_nonneg (Real.rpow_nonneg
      (torusParabolicSize_nonneg _) _) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have s := ty.add (g := fun w => i2Psi2Slab x.1 w *
      (torusParabolicSize (x - w) ^ (-(3 + θ)) * torusParabolicSize (g₁ - w) ^ (-l₁) *
        torusParabolicSize (g₂ - w) ^ (-l₂))) (m y).aemeasurable (n y) (n x) hCT hCT tx
  have c := s.const_mul (c := 12 * B * torusParabolicSize (y - x) ^ θ)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
    with w hyw hxw
  have h := abs_kernel_sub_le_slab hB hθ0 hθ1 hKs hKb hKi hxy hyw hxw
  have n2 : 0 ≤ torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂) :=
    weight_mul_nonneg g₁ g₂ _ _ w
  calc |K (y - w) - K (x - w)| * (torusParabolicSize (g₁ - w) ^ (-l₁) *
          torusParabolicSize (g₂ - w) ^ (-l₂))
      ≤ (i2Psi2Slab x.1 w * (12 * B * torusParabolicSize (y - x) ^ θ *
        (torusParabolicSize (y - w) ^ (-(3 + θ)) + torusParabolicSize (x - w) ^ (-(3 + θ))))) *
          (torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂)) :=
        mul_le_mul_of_nonneg_right h n2
    _ = _ := by ring
end RegularityStructures
end

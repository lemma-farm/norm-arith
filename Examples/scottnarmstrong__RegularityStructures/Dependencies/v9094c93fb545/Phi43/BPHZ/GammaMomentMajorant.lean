/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.Phi43.BPHZ.TreeI2Psi2DiagramMultiSq
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Lower-integral bounds for kernels with a pointwise majorant

The estimates of `TreeI2Psi2DiagramMulti*` are stated for the increment of a kernel `K` of order
`3`.  We prove the same estimates for an arbitrary kernel `A` (a gradient increment, a Taylor
remainder, ...) that is only known through the pointwise majorant

`|A w| ≤ slab(w) * M * r^a * (s(y - w)^(-p) + s(x - w)^(-p))`,

where `slab(w) = 1` for `|w₀ - x₀| ≤ 2` and `0` otherwise (`gammaMajorant`).  The exponent `p` is
the decay of `A` at its singularities and `a` the gain in `r = s(y - x)`; they are independent.

* `gammaMajorant_lint_single`: `∫ |A| s(g - w)^(-e) ≲ M r^a (s(y-g)^(-(p+e-5)) + s(x-g)^(-(p+e-5)))`
  for `0 < p < 5`, `0 < e < 5`, `p + e > 5`;
* `gammaMajorant_lint_slab`: `∫ |A| s(g₁ - w)^(-l₁) s(g₂ - w)^(-l₂) ≲ M r^a` for `p + l₁ + l₂ < 5`;
* `gammaMajorant_lint_diag`: `∬ |A(w)| |A'(w')| s(w' - w)^(-e) ≲ M M' r^a r'^a'`.
-/
@[expose] public section
open MeasureTheory
namespace RegularityStructures.Phi43
open RegularityStructures
/-- The pointwise majorant `|A w| ≤ slab * M r^a (s(y-w)^(-p) + s(x-w)^(-p))`, `r = s(y-x)`. -/
def gammaMajorant (A : SpaceTime → ℝ) (x y : SpaceTime) (r M a p : ℝ) : Prop :=
  0 ≤ r ∧ 0 ≤ M ∧ Measurable A ∧ ∀ w : SpaceTime, 0 < torusParabolicSize (y - w) →
    0 < torusParabolicSize (x - w) →
      |A w| ≤ i2Psi2Slab x.1 w * (M * r ^ a *
        (torusParabolicSize (y - w) ^ (-p) + torusParabolicSize (x - w) ^ (-p)))
end RegularityStructures.Phi43
end
public section
open MeasureTheory
namespace RegularityStructures.Phi43
open RegularityStructures
private theorem gmaj_measurable_weight (p g : SpaceTime) (a b : ℝ) :
    Measurable fun w : SpaceTime => torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  (measurable_torusParabolicSize_sub_rpow p a).mul (measurable_torusParabolicSize_sub_rpow g b)
private theorem gmaj_weight_nonneg (p g : SpaceTime) (a b : ℝ) (w : SpaceTime) :
    0 ≤ torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
/-- **Majorant kernel against `s(g - w)^(-e)`.** -/
theorem gammaMajorant_lint_single {a p e : ℝ} (hp : 0 < p) (hp5 : p < 5) (he : 0 < e)
    (he5 : e < 5) (hpe : 5 < p + e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : SpaceTime → ℝ} {x y : SpaceTime} {r M : ℝ},
      gammaMajorant A x y r M a p → ∀ g : SpaceTime, 0 < torusParabolicSize (y - g) →
        0 < torusParabolicSize (x - g) →
        i2Psi2LintBound volume (fun w => |A w| * torusParabolicSize (g - w) ^ (-e))
          (C * M * r ^ a *
            (torusParabolicSize (y - g) ^ (-(p + e - 5)) +
              torusParabolicSize (x - g) ^ (-(p + e - 5)))) := by
  obtain ⟨CG, hCG, hG⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := p) (b := e) hp hp5 he he5 hpe
  refine ⟨CG, hCG, ?_⟩
  intro A x y r M hA g hyg hxg
  obtain ⟨hr0, hM, -, hAb⟩ := hA
  have e0 : (5 : ℝ) - p - e = -(p + e - 5) := by ring
  have gy := hG y g hyg
  have gx := hG x g hxg
  rw [e0] at gy gx
  have s := gy.add (g := fun w => torusParabolicSize (x - w) ^ (-p) *
      torusParabolicSize (g - w) ^ (-e)) (gmaj_measurable_weight y g _ _).aemeasurable
    (gmaj_weight_nonneg y g _ _) (gmaj_weight_nonneg x g _ _)
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) gx
  have hr := Real.rpow_nonneg hr0 a
  have c := s.const_mul (c := M * r ^ a) (mul_nonneg hM hr)
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
    with w hy hx
  have h := hAb w hy hx
  have n2 : 0 ≤ torusParabolicSize (g - w) ^ (-e) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hsl := i2Psi2Slab_le_one x.1 w
  have hsum : 0 ≤ M * r ^ a * (torusParabolicSize (y - w) ^ (-p) +
      torusParabolicSize (x - w) ^ (-p)) :=
    mul_nonneg (mul_nonneg hM hr) (add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  calc |A w| * torusParabolicSize (g - w) ^ (-e)
      ≤ (M * r ^ a * (torusParabolicSize (y - w) ^ (-p) +
        torusParabolicSize (x - w) ^ (-p))) * torusParabolicSize (g - w) ^ (-e) :=
        mul_le_mul_of_nonneg_right (h.trans (mul_le_of_le_one_left hsum hsl)) n2
    _ = _ := by ring
end RegularityStructures.Phi43
end

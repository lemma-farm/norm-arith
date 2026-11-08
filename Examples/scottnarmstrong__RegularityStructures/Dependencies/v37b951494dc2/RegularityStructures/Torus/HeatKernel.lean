/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Torus.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Heat kernels on the three-torus

* `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`, the heat kernel on `ℝ³`;
* `heatKernel t`, its periodisation `p_t` on `T³` (the statement, equation (2.1));
* `heatSemigroup s f`, the heat semigroup `P_s` acting on `C(T³)` by convolution with the Gaussian
  on `ℝ³`;
* `massiveHeatKernel`, the kernel `G(t, x) = 1_{t>0} e^{-t} p_t(x)` of `(∂_t - Δ + 1)⁻¹`
  (equation (2.2)).

The lemmas show that `gaussKernel s` is a probability density for `s > 0`, so `P_s` is linear
and contracts the supremum norm.

Source: the statement, Section 2.
-/
@[expose] public noncomputable section
open MeasureTheory Real
namespace RegularityStructures
/-- The heat kernel on `ℝ³`: `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`. -/
def gaussKernel (t : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (4 * π * t) ^ (-(3 : ℝ) / 2) * exp (-sqNorm3 y / (4 * t))
end RegularityStructures
end
/-! ### The Gaussian density on `ℝ³` -/
public section
open MeasureTheory Real
namespace RegularityStructures
theorem gaussKernel_eq_prod (t : ℝ) (y : Fin 3 → ℝ) :
    gaussKernel t y = (4 * π * t) ^ (-(3 : ℝ) / 2) * ∏ i, exp (-(4 * t)⁻¹ * y i ^ 2) := by
  have h : -(∑ i, y i ^ 2) / (4 * t) = ∑ i, -(4 * t)⁻¹ * y i ^ 2 := by
    rw [← Finset.mul_sum]
    ring
  rw [gaussKernel, ← Real.exp_sum, sqNorm3, h]
theorem gaussKernel_nonneg {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) : 0 ≤ gaussKernel t y := by
  unfold gaussKernel
  have : 0 < 4 * π * t := by positivity
  positivity
theorem integrable_gaussKernel {s : ℝ} (hs : 0 < s) : Integrable (gaussKernel s) := by
  have hb : 0 < (4 * s)⁻¹ := by positivity
  have h := Integrable.fintype_prod (ι := Fin 3) (μ := fun _ => (volume : Measure ℝ))
    (f := fun _ v => exp (-(4 * s)⁻¹ * v ^ 2)) fun _ => integrable_exp_neg_mul_sq hb
  have h' := h.const_mul ((4 * π * s) ^ (-(3 : ℝ) / 2))
  refine h'.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [gaussKernel_eq_prod]
theorem integral_gaussKernel {s : ℝ} (hs : 0 < s) : ∫ y, gaussKernel s y = 1 := by
  have ha : 0 < 4 * π * s := by positivity
  simp_rw [gaussKernel_eq_prod]
  rw [integral_const_mul]
  rw [integral_fintype_prod_volume_eq_pow (ι := Fin 3) (fun v : ℝ => exp (-(4 * s)⁻¹ * v ^ 2)),
    integral_gaussian, Fintype.card_fin]
  have hpi : π / (4 * s)⁻¹ = 4 * π * s := by field_simp
  rw [hpi, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
  norm_num
/-! ### The heat semigroup -/
end RegularityStructures
end

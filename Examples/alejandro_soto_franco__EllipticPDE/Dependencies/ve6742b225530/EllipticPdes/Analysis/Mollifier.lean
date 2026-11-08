/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The standard mollifying family

On a finite-dimensional real normed space `E` with an additive Haar measure `μ`, the family
`mollifier hr n` of bumps of outer radius `r / (n + 1)` mollifies any locally integrable
function `h : E → F` into a `C^∞` function, with compact support when `h` has compact support,
bounded by the supremum of `h`, and supported in the closed thickening of the support of `h` by
the radius of the bump.

## Main declarations

* `EllipticPdes.mollifier`: the bump of outer radius `r / (n + 1)` and inner radius half of it.
* `EllipticPdes.tendsto_rOut_mollifier`, `EllipticPdes.rOut_mollifier_le`: the radii shrink.
* `EllipticPdes.contDiff_normed_convolution`: a mollification is smooth.
* `EllipticPdes.norm_normed_convolution_le`: a mollification is bounded by what it mollifies.
* `EllipticPdes.tsupport_normed_convolution_subset`: the support of a mollification.
-/
@[expose] public section
open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal Convolution Pointwise
noncomputable section
namespace EllipticPdes
section Radii
variable {E : Type*} [NormedAddCommGroup E]
/-- The `n`-th bump of the standard mollifying family of scale `r`, of outer radius
`r / (n + 1)` and inner radius half of it. -/
def mollifier {r : ℝ} (hr : 0 < r) (n : ℕ) : ContDiffBump (0 : E) where
  rIn := r / (n + 1) / 2
  rOut := r / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)
/-- The outer radius of `mollifier hr n` is `r / (n + 1)`. -/
@[simp] theorem rOut_mollifier {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (mollifier hr n : ContDiffBump (0 : E)).rOut = r / (n + 1) := rfl
theorem rOut_mollifier_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (mollifier hr n : ContDiffBump (0 : E)).rOut ≤ r := by
  rw [rOut_mollifier]
  exact div_le_self hr.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
theorem tendsto_rOut_mollifier {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => (mollifier hr n : ContDiffBump (0 : E)).rOut) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv, mul_comm] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r
end Radii
section Convolution
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
end Convolution
end EllipticPdes

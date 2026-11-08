module
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.Semigroup
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.DoobKernel
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.Hyperbolic
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Connecting the Gaussian Doob transform to the heat kernel

The equations below connect actual Gaussian expectations and actual heat
convolution. They establish the analytic identities in the proof of
Proposition 5.5, without asserting an SDE transition-law identification.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
theorem kernelAverage_heatKernel_eq_gaussian_integral
    (v : ℝ≥0) (hv : v ≠ 0) (k : ℝ → ℝ) (x : ℝ) :
    kernelAverage (μ := volume) (heatKernel v) k x = ∫ y, k y ∂gaussianReal x v := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [kernelAverage, heatKernel_eq_gaussianPDFReal, smul_eq_mul]
end Paper

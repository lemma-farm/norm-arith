module
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.GaussianPositivity
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
@[expose] public section
/-!
# Independent Gaussian sums and heat convolution

The independent pair uses the genuine product Gaussian probability measure.
The affine sum law is proved by Gaussian convolution, including zero
coefficients. Boundedness supplies the product integrability needed for Fubini.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
noncomputable def standardGaussianPair : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)
instance : IsProbabilityMeasure standardGaussianPair := by
  unfold standardGaussianPair
  infer_instance
end Paper

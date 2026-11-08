module
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.GaussianDifferentiation
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.GaussianIBP
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.GaussianPositivity
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Gaussian heat derivatives and joint continuity

The variance derivative is proved by dominated differentiation in the Gaussian
scale, followed by the actual standard-Gaussian Stein identity. The square-root
chain rule is used only at strictly positive variance.
-/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper
theorem integrable_standardGaussian_id : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
  apply integrable_of_mem_interior_integrableExpSet (X := fun z : ℝ => z)
  simp [integrableExpSet_fun_id_gaussianReal]
end Paper

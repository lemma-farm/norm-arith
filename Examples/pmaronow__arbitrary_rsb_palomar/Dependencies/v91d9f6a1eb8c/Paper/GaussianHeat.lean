module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.GaussianDifferentiation
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.GaussianIBP
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.GaussianPositivity
public import Mathlib.Analysis.SpecialFunctions.Sqrt
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

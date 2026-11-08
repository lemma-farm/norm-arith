module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourHolderAlgebra
/-!
# Actual Hölder-norm continuity of inversion and boundary phases

The inverse-difference identity is an equality of actual Hölder functions.
The bounded pointwise product gives its norm estimate.  This proves genuine
inverse convergence under a common positive pointwise lower bound, and a
uniform Lipschitz estimate when the Hölder norms also have a common bound.
The actual phase `conj g / g` is continuous in the same Hölder norm.
-/
@[expose] public section
noncomputable section
open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction ComplexConjugate
namespace Euler2D.HolderFunctionSpace
variable {X : Type*} [MetricSpace X] {γ : ℝ≥0}
end Euler2D.HolderFunctionSpace
end

module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourCauchyShapeEstimates
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourCauchyOperator
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourDerivativePhaseContinuity
/-! # Genuine Hölder operator-norm continuity in the contour -/
@[expose] public section
noncomputable section
open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Euler2D
local instance (priority := 2000) shapeC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) shapeC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)
end Euler2D
end

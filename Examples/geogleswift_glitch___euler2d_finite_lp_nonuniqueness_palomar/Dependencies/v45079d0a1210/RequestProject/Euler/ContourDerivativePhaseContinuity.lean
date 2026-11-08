module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourDerivativePhase
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourHolderInverseContinuity
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourAdmissibility
/-!
# Hölder-norm continuity of the actual contour derivative phase

The phase is literally `conj Z' / Z'`.  Positive short-chord bounds give
the common positive lower derivative bound needed for genuine Hölder-norm
inversion.  Its value is independent of the chosen chord constant.
-/
@[expose] public section
noncomputable section
open Set Filter Topology Metric
open scoped NNReal ComplexConjugate
namespace Euler2D
local instance (priority := 2000) contourPhase_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
variable {γ : ℝ≥0}
end Euler2D
end

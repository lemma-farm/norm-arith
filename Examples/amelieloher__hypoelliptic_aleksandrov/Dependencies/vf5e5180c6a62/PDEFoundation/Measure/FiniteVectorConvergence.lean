module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Ambient.EuclideanNorm
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite-vector `L^p` convergence

This file turns coordinatewise `L^p` convergence of native vector fields into
`L^p` convergence of their explicit Euclidean magnitudes.  The finite
coordinate sum is used only as a convergence majorant; the resulting norm is
the exact Euclidean norm and carries no comparison constant.
-/
@[expose] public section
open scoped ENNReal
namespace PDE
open MeasureTheory
end PDE

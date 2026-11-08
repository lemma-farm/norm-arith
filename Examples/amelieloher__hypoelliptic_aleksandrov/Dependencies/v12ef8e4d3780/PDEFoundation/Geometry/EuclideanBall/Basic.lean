module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.PDEFoundation.Ambient.EuclideanNorm
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.PDEFoundation.Geometry.Affine
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Round balls on native vectors

Round balls are defined through the explicit Euclidean squared distance, not
the inherited finite-product metric. The squared-radius convention agrees
with the established homogenization API. Consequently, norm-membership and
radius-monotonicity lemmas state the required radius sign assumptions.
-/
@[expose] public section
open scoped Pointwise
namespace PDE
end PDE

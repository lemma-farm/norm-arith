module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Geometry.ConvexSegment
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Convex-domain smoothing geometry

This file isolates the affine sampling map used by convex-domain smooth
approximation. Given an internal base
`Metric.closedBall x0 r ⊆ U`—a cube for the inherited supremum metric—the
map samples a function at

`(1 - ε) • x + ε • (x0 - r • z)`.

If `‖z‖ ≤ 1` and `0 ≤ ε ≤ 1`, the second endpoint lies in that base cube,
and convexity keeps the sample point in `U`.
-/
@[expose] public section
namespace PDE
end PDE

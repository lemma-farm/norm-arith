module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Geometry.Affine
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Geometry.Domain
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Geometry.EuclideanBall
public import Mathlib
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Bounded open convex domains

The shared domain class for mean-zero Poincaré and Sobolev--Poincaré
estimates. It contains explicit round balls and axis-aligned cubes.
-/
@[expose] public section
open scoped Pointwise
namespace PDE
def IsOpenBoundedConvexDomain {d : ℕ}
    (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U
namespace IsOpenBoundedConvexDomain
end IsOpenBoundedConvexDomain
end PDE

module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Geometry.ConvexDomain
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Segment geometry in convex domains

This file provides the affine parametrization of a segment and the elementary
lemmas needed to keep that segment inside a convex domain. It contains no
Sobolev or Poincaré theory.

## Main definitions

- `PDE.segmentBlend`: the point with parameter `t` on the segment from `y` to `x`.

## Main results

- `PDE.segmentBlend_mem`: a segment between two points of a convex set stays in the set.
- `PDE.segmentBlend_mapsTo`: the corresponding `Set.MapsTo` statement.
- `PDE.ray_mem_of_endpoint_mem_of_isOpenBoundedConvexDomain`: a shorter point on a
  nonnegative ray remains in the domain when the endpoint does.
-/
@[expose] public section
namespace PDE
end PDE

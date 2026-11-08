/-
# Boundary reduction for the scalar Crouzeix companion

The scalar companion is holomorphic in the interior of a smooth Jordan
domain, but its defining contour integral is singular on the boundary.  The
Plemelj step therefore naturally supplies a separate continuous extension to
the closed domain.  This file proves that any such extension automatically
inherits the companion's interior differentiability.  The maximum-modulus
principle then reduces the sharp interior contraction entirely to a frontier
bound for the extension.

No boundary-value theorem is assumed implicitly: both continuity on the
closure and the frontier estimate remain explicit hypotheses.

## Main declarations

* `crouzeixPolynomialScalarCompanionClosedExtension` -- the canonical
  limit-based extension from the open carrier.
* `continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto`
  -- pointwise interior limits on the frontier make that extension continuous.
* `diffContOnCl_crouzeixPolynomialScalarCompanion_extension` -- a continuous
  closed-domain extension is differentiable in the interior.
* `norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary` -- a
  frontier bound propagates across the closed domain.
* `norm_crouzeixPolynomialScalarCompanion_le_of_boundary_extension` -- the
  resulting bound for the actual interior companion.
* `norm_crouzeixPolynomialScalarCompanion_le_of_boundary_tendsto` -- the same
  sharp reduction stated directly in terms of Plemelj boundary limits.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.ScalarCompanion
import Mathlib
import Mathlib.Topology.ExtendFrom
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Filter Set

module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.W1p.ConvexApprox.Continuity
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Pointwise bounds for convex-domain smoothing

This file proves constant and zero-scale identities for convex approximation,
the weighted-difference representation of its error, and pointwise bounds in
terms of oscillation and a modulus of continuity. It then upgrades the bounds
to uniform-on-domain convergence along arbitrary admissible scale sequences
and the canonical unit sequence.

## Main results

* `PDE.abs_convexApproxSmoothing_sub_le_of_modulus` controls the error by a
  supplied modulus on the bounded convex domain.
* `PDE.eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous`
  gives uniform-on-domain convergence along any admissible scale sequence.
* `PDE.eventually_forall_abs_unitConvexApproxSequence_sub_le_of_continuous`
  specializes the uniform bound to the canonical unit sequence.
* `PDE.tendsto_unitConvexApproxSequence_of_continuous` gives pointwise
  convergence at every point of the domain.
-/
@[expose] public section
open scoped Pointwise Convolution
namespace PDE
end PDE

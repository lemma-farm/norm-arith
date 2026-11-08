module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.ConvexApprox.WeakDerivSmoothing
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Continuity of convex-domain smoothing

This file closes the weak-derivative smoothing chain by identifying the
classical coordinate derivatives of the smooth representative almost
everywhere. It also records the elementary continuity, support, and
integrability facts used by pointwise bounds and `L^p` convergence.

The separate classical-input differentiation-under-the-integral theory is not
part of this foundational module.
-/
@[expose] public section
open scoped Pointwise Convolution
namespace PDE
end PDE

module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.ConvexApprox.WeakDerivSmoothing.Affine
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Averaging weak derivatives over a convex smoothing kernel

Compact local integrability and Fubini give the exact smoothing derivative identity.
-/
@[expose] public section
open scoped Pointwise
namespace PDE
namespace HasWeakPartialDerivOn
end HasWeakPartialDerivOn
namespace HasWeakGradientOn
end HasWeakGradientOn
end PDE

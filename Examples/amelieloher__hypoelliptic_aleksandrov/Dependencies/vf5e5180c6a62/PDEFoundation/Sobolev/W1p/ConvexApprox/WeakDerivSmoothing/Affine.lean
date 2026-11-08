module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.ConvexApprox.SmoothRepresentative
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.WeakDerivative.Affine
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.WeakDerivative.Algebra
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Affine transport for convex-domain smoothing

Precomposition by each fixed convex-approximation sampling map transports weak
partial derivatives and weak gradients with the exact affine factor `1 - ε`.
-/
@[expose] public section
open scoped Pointwise
namespace PDE
namespace HasWeakPartialDerivOn
end HasWeakPartialDerivOn
namespace HasWeakGradientOn
end HasWeakGradientOn
end PDE

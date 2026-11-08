module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.AffineVolume
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.WeakDerivative
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Affine transport of weak first derivatives

Translation is exact: precomposing values and gradients by `x ↦ x - z`
transports a weak derivative from `U` to `z + U`.
-/
@[expose] public section
open scoped Pointwise
namespace PDE
namespace HasWeakPartialDerivOn
end HasWeakPartialDerivOn
namespace HasWeakGradientOn
end HasWeakGradientOn
end PDE

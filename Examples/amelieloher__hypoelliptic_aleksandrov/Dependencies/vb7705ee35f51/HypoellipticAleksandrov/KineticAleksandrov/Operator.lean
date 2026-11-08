module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.Parabolic.KineticClassical
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Kinetic Aleksandrov operators

This module records the three operator surfaces used by the kinetic
Aleksandrov source.  `backwardOperator` is the full kinetic operator
`∂ₜ + v · ∇ₓ - A : Dᵥ²`, while `transportedForwardOperator` is the forward
operator `∂σ + B : Dᵧ² + b(y) · ∇z`.

For the transported operator, `KineticPoint n` is read as the ordered triple
`(σ, y, z)`: its `position` field is the diffused `y` coordinate and its
`velocity` field is the transported `z` coordinate.  The derivative APIs are
the existing ones on `KineticPoint`; no second point or derivative hierarchy
is introduced.  The W/I domain and structural alternatives belong to a
separate setting conditions, not to these literal operator definitions.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov
open HypoellipticAleksandrov.Parabolic
end HypoellipticAleksandrov.KineticAleksandrov

module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.LocalClassical
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Exponential time conjugation for the forward parabolic operator

Multiplication by `exp (rho * (t - tBase))` removes a zeroth-order term from
the project-sign operator `∂t - A : Dv²`.  The identities are local in the
scalar function and impose no sign condition on `rho`, coefficient
regularity, ellipticity, or parabolic estimate.
-/
@[expose] public section
namespace HypoellipticAleksandrov.Parabolic
noncomputable section
open Filter
open scoped Topology
end
end HypoellipticAleksandrov.Parabolic

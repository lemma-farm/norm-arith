module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.HarnackABP
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.EllipticityClosure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Local geometry for the near-one density argument

This file records the coordinate containments and boundary-closure facts for
the fixed local ABP cylinder used in the near-one density-to-point argument.
It contains no PDE estimate or barrier operator calculation.
-/
@[expose] public section
open Filter Set
open scoped Topology
namespace HypoellipticAleksandrov.Parabolic
noncomputable section
end
end HypoellipticAleksandrov.Parabolic

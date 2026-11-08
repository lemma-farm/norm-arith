module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDualPairing
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Local convergence of reverse-time Steklov dual pairings

This module combines the local Bochner Steklov approximation with
the reverse-time `V*`--`V` pairing.  It makes no fixed-time representative,
trace, weak-derivative, or energy assertion.
-/
@[expose] public section
open Filter MeasureTheory Set Topology
open scoped ENNReal
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet

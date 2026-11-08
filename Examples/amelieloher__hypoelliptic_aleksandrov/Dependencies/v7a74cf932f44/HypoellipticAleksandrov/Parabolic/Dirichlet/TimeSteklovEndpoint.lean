module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Endpoint-safe reverse-time Steklov convergence

This module upgrades the strict-interior Steklov convergence theorem to the
whole closed time interval.  The proof uses the zero extension only inside
ordinary Lebesgue integrals, so no endpoint values are interpreted as traces.
-/
@[expose] public section
open Filter MeasureTheory Set Topology
open scoped ENNReal
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet

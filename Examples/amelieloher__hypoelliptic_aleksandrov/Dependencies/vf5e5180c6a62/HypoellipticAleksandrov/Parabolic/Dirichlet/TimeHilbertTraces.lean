module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertRepresentative
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Canonical reverse-time Hilbert traces

This module selects the continuous spatial-`L²` representative of a
reverse-time Gelfand curve and evaluates that representative at the two closed
time endpoints. These are not evaluations of the raw Bochner representative.
-/
@[expose] public section
open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet

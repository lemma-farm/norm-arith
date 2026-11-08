module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEndpoint
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
public import Mathlib
public import Mathlib.Topology.ContinuousMap.Compact
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Hilbert-valued reverse-time Steklov curves

This module packages the literal one-sided Steklov averages as continuous
Hilbert-valued curves on closed time collars.
-/
@[expose] public section
open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet

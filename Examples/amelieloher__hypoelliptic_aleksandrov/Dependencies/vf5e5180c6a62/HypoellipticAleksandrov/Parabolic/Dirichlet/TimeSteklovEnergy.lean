module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandSteklov
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Reverse-time Steklov energy identities

This module proves the fixed-positive-step Hilbert-value energy identities for
forward and backward reverse-time Steklov averages in the spatial Gelfand
triple.  It does not assert an energy identity for an unregularized curve.
-/
@[expose] public section
open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet

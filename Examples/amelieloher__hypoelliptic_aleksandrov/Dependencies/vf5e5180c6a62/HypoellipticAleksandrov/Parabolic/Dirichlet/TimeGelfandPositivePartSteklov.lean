module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePartContinuity
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
# Positive-part reverse-time Steklov energy identities

This module proves the fixed-window energy identities for the positive part of
forward and backward reverse-time Steklov averages.  The chain rule is obtained
from the convex support inequalities for the squared `L²` norm of the positive
part; no derivative of the positive-part curve is asserted.
-/
@[expose] public section
open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet

module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.va265c9eac07b.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandAffine
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.va265c9eac07b.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Reverse-time Gelfand--Steklov calculus

This module transfers the almost-everywhere reverse-time Gelfand affine
identity through literal Steklov windows.  Its derivative formulas concern
only the resulting regularized dual curves, not pointwise representatives of
the underlying `Lp` curves.
-/
@[expose] public section
open Filter Function MeasureTheory Set Topology
open scoped ENNReal
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet

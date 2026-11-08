module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTranslation
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# One-sided reverse-time Bochner averages

This module provides literal reverse-time Bochner Steklov windows and their
basic regularity.  The local strong approximation assertions are stated on
strictly interior compact intervals, so they remain assertions about `Lp`
classes rather than selected pointwise representatives.
-/
@[expose] public section
open Filter MeasureTheory Set Topology
open scoped ENNReal
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet

module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import Mathlib
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Scalar reverse-time distribution separation

This module transfers scalar distribution separation on an open interval from
ambient Lebesgue measure to the literal restricted reverse-time measure.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Filter MeasureTheory Set
open scoped ENNReal
end HypoellipticAleksandrov.Parabolic.Dirichlet

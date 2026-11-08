module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v80cc261cd169.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Series
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v80cc261cd169.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.IntegralKernel
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Positive integral definitions of Kummer U

`UI` has positive shape and argument. `UN` is the source transformation for the
negative shape interval. The real auxiliary formulae are only characterized at positive
arguments; their values outside that domain are never used as special-function values.
-/
@[expose] public noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

module
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The confluent hypergeometric power series

Literal real and complex series for Kummer M, with positive denominator parameter.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
/-- Positive real parameters. -/
abbrev Pos := {x : ℝ // 0 < x}
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

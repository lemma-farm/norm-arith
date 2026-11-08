module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v80cc261cd169.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Integral
public import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Polynomially bounded Taylor remainder for a translated power

Analyticity controls the remainder at zero. A polynomial growth bound then extends it
to the entire nonnegative half-line, as required for domination of Laplace remainders.
-/
@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
/-- Literal Taylor polynomial of the translated power, truncated before order N. -/
def powerTaylor (q : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Ring.choose q n * t ^ n
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

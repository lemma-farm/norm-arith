module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.GaussianDifferentiation
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
/-!
# Strict positivity of odd-function Gaussian expectations

For a positive Gaussian mean, reflection makes an odd function's expectation
positive when it is strictly positive on the positive half-line. The proof
uses genuine Gaussian densities and Lebesgue integrals. The full-line
symmetrization avoids auxiliary set-integral boundary arguments.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
end Paper

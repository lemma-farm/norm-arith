module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Mathlib
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v33f92a46e50d.Lemmas.SpinGlass.GaussianIntegrationByParts
set_option autoImplicit true
set_option linter.deprecated false
@[expose] public section
open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal
open scoped Topology
set_option autoImplicit false
namespace SpinGlass.AT
end SpinGlass.AT

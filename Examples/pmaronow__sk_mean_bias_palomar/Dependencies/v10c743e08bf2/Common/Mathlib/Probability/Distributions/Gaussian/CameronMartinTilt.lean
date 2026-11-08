module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v10c743e08bf2.Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinThm
public import Mathlib
set_option autoImplicit false
@[expose] public section
/- Adaptation: declarations are placed in ColeHopfFoundation to avoid duplicate names when imported alongside the independently sourced RSAT library. -/
namespace ColeHopfFoundation
open _root_.MeasureTheory
open _root_.ProbabilityTheory
/-!
# Cameron–Martin: scalar-parameter form

Cameron–Martin theorem specialized to translations `t • x`.
-/
open MeasureTheory Filter Complex
open scoped _root_.ENNReal _root_.NNReal _root_.Topology _root_.InnerProductSpace
namespace ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]
end ProbabilityTheory
end ColeHopfFoundation

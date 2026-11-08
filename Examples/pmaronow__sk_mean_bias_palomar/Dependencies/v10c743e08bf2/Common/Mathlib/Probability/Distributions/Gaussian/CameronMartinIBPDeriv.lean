module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v10c743e08bf2.Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBP
public import Mathlib
set_option autoImplicit false
@[expose] public section
/- Adaptation: declarations are placed in ColeHopfFoundation to avoid duplicate names when imported alongside the independently sourced RSAT library. -/
namespace ColeHopfFoundation
open _root_.MeasureTheory
open _root_.ProbabilityTheory
/-!
# Cameron–Martin IBP: abstract step

If tilt equals shift near `0` and both are differentiable at `0`, uniqueness of derivatives yields
Gaussian IBP. Main: `cameronMartin_integral_by_parts_of_hasDerivAt`.
-/
open MeasureTheory Filter
open scoped _root_.Topology
namespace ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]
/-! ## IBP as “derivative of tilt = derivative of shift” -/
end ProbabilityTheory
end ColeHopfFoundation

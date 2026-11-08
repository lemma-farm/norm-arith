module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Semigroup
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.DoobKernel
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Hyperbolic
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Connecting the Gaussian Doob transform to the heat kernel

The equations below connect actual Gaussian expectations and actual heat
convolution. They establish the analytic identities in the proof of
Proposition 5.5, without asserting an SDE transition-law identification.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
end Paper

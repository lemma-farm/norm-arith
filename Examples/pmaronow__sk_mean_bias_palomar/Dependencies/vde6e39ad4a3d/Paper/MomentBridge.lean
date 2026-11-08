module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Structural
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.HeatContraction
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Variational
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Analytic Doob moments and the conditional right-hand bound

The moments in this file are literal Gaussian integrals of the proven positive,
normalized Gaussian Doob operator. Their initial values, moment comparison,
and exponential decay are proved. Transition-law identification with the
paper's diffusion and the Itô derivative identity remain explicit hypotheses.
This file does not assert Proposition 5.1 or identify an SDE solution.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
end Paper

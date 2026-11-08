module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.SoftMoment
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.DoobDifferentiation
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Concrete RS second moment and its variational minimum

The pre-interface Gaussian conditional second moment and the post-interface
Gaussian Doob second moment are assembled into a continuous real function.
Gaussian Poincaré, Gaussian heat differentiation, and the moment comparison
prove its two signs and the minimum of the actual variational integral.
No Poincaré, Itô, transition-law, or regularity hypothesis is assumed here.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Paper
end Paper

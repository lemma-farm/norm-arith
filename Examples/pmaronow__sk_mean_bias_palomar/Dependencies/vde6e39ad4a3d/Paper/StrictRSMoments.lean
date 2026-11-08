module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.RSMoments
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Strict post-interface moment and variational inequalities

Positivity of the actual Doob fourth moment makes the second moment strictly
increasing. In the small-variance regime this turns the comparison derivative
bound into a strict bound. The existing exponential estimate handles the
remaining regime, so strictness holds under the original fixed-point and AT
assumptions without an additional small-field hypothesis.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
end Paper

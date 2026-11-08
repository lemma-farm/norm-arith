module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.MomentBridge
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.GaussianHeat
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Derivatives of the concrete analytic hard moments

The post-`q` moment identity is proved from Gaussian heat differentiation and
cosh normalization, without an Itô formula or a diffusion-law hypothesis.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ContDiff
namespace Paper
end Paper

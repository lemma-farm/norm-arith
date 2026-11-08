module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.QuadraticEnergy
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# The adaptive functional and its exact Taylor remainder

The two contact losses are the squares of the negative and positive parts
of the actual affine momenta. Their Bregman remainders are nonnegative.
Consequently a stationary pair is the unique maximizer among pairs with the
same four endpoint values. This file proves that analytic implication; it
does not assume or assert existence of a stationary pair at every width, a
global width maximum, or a comparison with the area of an arbitrary cap.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa.Analysis
attribute [local fun_prop] QuarterPair.continuous_f QuarterPair.continuous_g
  QuarterPair.continuous_fD QuarterPair.continuous_gD
def QuarterPair.p (u : QuarterPair) (t : ℝ) : ℝ := u.fD t - u.g t + 1
def QuarterPair.q (u : QuarterPair) (t : ℝ) : ℝ := u.gD t + u.f t - 1
end AmbidextrousSofa.Analysis

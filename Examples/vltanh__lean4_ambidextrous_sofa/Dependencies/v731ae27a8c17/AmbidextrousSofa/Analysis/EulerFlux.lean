module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.AdaptiveFunctional
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Euler flux and the first-variation boundary identity

The stationary condition is obtained from actual derivative equations by
the fundamental theorem of calculus. The same proof records the boundary
terms for variations that change the width.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa.Analysis
attribute [local fun_prop] QuarterPair.continuous_f QuarterPair.continuous_g
  QuarterPair.continuous_fD QuarterPair.continuous_gD
end AmbidextrousSofa.Analysis

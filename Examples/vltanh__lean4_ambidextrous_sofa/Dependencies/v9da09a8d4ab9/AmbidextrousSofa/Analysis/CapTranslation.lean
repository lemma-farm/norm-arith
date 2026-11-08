module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Measure.CapScore
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Measure.RigidInvariance
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Horizontal translation of actual cap scores

Every roof, support wall, and moving integration window is translated by
the same amount. Product Lebesgue translation invariance therefore leaves
the full or partial spatial score unchanged. This permits compact-domain
normalization without imposing symmetry on a competitor.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa

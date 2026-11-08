module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.ExactEstimates
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Initial-floor energy for tilted supports

The two energy tests are derived from the actual zero-density momentum
circle, stopped at either the floor or the first zero of the first
momentum. Energy propagation uses absolutely continuous momenta and their
almost-everywhere source equations. No continuity of the curvature
densities, optimizing profile, or sharp value certificate is assumed.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa.Analysis
end AmbidextrousSofa.Analysis

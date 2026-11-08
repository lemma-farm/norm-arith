module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapCompactness
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Area continuity for compact convex caps

Interior points eventually belong to every nearby cap. Exterior points
eventually stay outside, and the frontier of a convex set has zero planar
measure. Dominated convergence in a common compact box then gives continuity
of the actual Lebesgue area, including lower-dimensional limiting caps.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
end AmbidextrousSofa

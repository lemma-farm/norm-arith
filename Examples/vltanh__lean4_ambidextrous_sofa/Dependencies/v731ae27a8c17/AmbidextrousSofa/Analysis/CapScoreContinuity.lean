module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapRoofConvergence
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapNicheContinuity
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Continuity of the full spatial cap score

The exterior roof and middle niche are integrated on the cap's own moving
projection window. Membership in those intervals stabilizes almost
everywhere. The roof is bounded by one; compact containment supplies a
uniform niche bound. Dominated convergence therefore applies to both terms.
-/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
namespace AmbidextrousSofa
end AmbidextrousSofa

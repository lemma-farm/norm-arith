module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapCompactness
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Geometry.BarrierAnalysis
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Joint continuity of the actual full-turn niche

The cap varies in the Hausdorff topology. At a zero denominator, the other
wall squeezes the positive part of the two-wall minimum to zero. The resulting
closed-angle maximum is exactly the niche defined by all open angles.
Consequently the niche is jointly continuous in the cap and the abscissa.
This argument includes caps of zero width or height.
-/
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace AmbidextrousSofa
end AmbidextrousSofa

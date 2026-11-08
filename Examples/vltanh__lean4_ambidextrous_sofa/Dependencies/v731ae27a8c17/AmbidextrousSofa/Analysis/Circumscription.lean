module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.AxisVariation
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Actual finite support circumscription

Intersecting the sampled support halfplanes with the actual projection
box produces a larger downward cap. Every sampled support remains exact,
and the actual projection is unchanged. Consequently the sampled physical
barrier and any sampled support penalty remain unchanged while the charged
exterior roof can only increase. These are the recovery competitors for
finite selected spatial maximizers.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace FinitePolygon
variable {ι : Type*}
end FinitePolygon
end AmbidextrousSofa

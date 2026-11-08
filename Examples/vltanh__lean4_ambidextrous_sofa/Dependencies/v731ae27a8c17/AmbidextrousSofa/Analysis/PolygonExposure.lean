module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.PolygonEnvelope
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Exposure inequality at an actual selected polygonal maximum

The maximization hypothesis concerns actual downward caps and their actual
support values. A positive floating facet supplies an admissible outward
family by `exists_outward_support_variation`. The finite roof and physical
barrier formulas then identify its ordinary derivative. The selection
penalty is a displayed finite quadratic sum, whose derivative is proved
here. Thus the exposure inequality is a consequence of maximization, not
an additional variational certificate.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace FinitePolygon
variable {ι : Type*}
end FinitePolygon
end AmbidextrousSofa

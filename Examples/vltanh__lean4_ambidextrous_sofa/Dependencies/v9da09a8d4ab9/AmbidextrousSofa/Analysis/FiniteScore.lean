module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.Circumscription
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.GridNiche
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Continuous finite spatial objectives and actual selected polygons

The finite objective retains the cap's own moving middle window. Its roof
integral is continuous by actual Hausdorff convergence of caps; its finite
physical barrier is jointly continuous. Compactness supplies an actual
maximizing cap. Circumscription preserves the sampled supports and improves
the charged roof, so it supplies an actual maximizing polygon in the same
box. No polygon existence or maximization field is assumed.
-/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
namespace AmbidextrousSofa
namespace FinitePolygon
variable {ι : Type*}
end FinitePolygon
end AmbidextrousSofa

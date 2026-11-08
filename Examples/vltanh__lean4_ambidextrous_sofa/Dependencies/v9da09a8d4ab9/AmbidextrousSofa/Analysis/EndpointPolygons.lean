module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.EndpointTrimming
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.PolygonEnvelope
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Inward endpoint operations preserve the finite polygon class

A cut only changes the two displayed endpoint walls. Horizontal erosion
tightens each displayed upper wall by the positive horizontal component
of its normal. These are exact identities of actual sets. The new displayed
heights need not be attained supports; replacing every height by its actual
support gives the same polygon, including redundant inequalities.
-/
noncomputable section
open Set
namespace AmbidextrousSofa
namespace FinitePolygon
variable {ι : Type*}
end FinitePolygon
end AmbidextrousSofa

module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Geometry.RigidMotion
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Geometry.Reflection
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Product Lebesgue area under rigid changes of coordinates

Rotation invariance follows from the determinant-one linear-map formula for
Haar measure. Translation and reflection are treated as actual coordinate
maps. These statements hold for all sets, and in particular do not require a
new measurability hypothesis on the original physical sofa.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa

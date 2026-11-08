module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Geometry.Support
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Geometry.HullCompact
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Geometry.Motions
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Actual hallway constraints and support tightening

The inner corner is excluded by a disjunction, while both outer walls must
hold. Tightening the two support offsets preserves every original retained
point; it does not assert that the entire convex hull fits the hallway.
The actual outgoing strip is tightened separately and remains a whole-body
condition. These are the pointwise geometric steps GA.1--GA.2 and GA.5.
-/
noncomputable section
namespace AmbidextrousSofa
end AmbidextrousSofa

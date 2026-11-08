module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapOrder
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Geometry.HullCompact
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Inserting a point into an actual downward cap

Insertion means convexifying the union with one point and filling its
vertical fibers down to the baseline. Supports in upward directions are
the maximum of the old support and the inserted point's coordinate pairing.
An inserted abscissa in the old projection preserves the exact projection.
-/
noncomputable section
open Set
namespace AmbidextrousSofa
end AmbidextrousSofa

module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.Extrusion
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Canonicalizing the uncharged middle roof

Intersecting a cap with the hypograph of a continuous concave ceiling is
an actual convex cap cut whenever the ceiling is nonnegative on its
projection. The chord through the middle-window endpoints lies below the
old roof inside that window and above it outside. Cutting to this chord
therefore preserves every charged exterior roof value and decreases the
actual barrier. Height saturation restores height one without lowering
the scalar score or destroying affinity of the middle roof.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa

module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Measure.CapScore
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Actual cap area and absolutely continuous primitives

A cap is the region under its attained roof, so Cavalieri gives its area,
which splits into two curved wings and a horizontal top face. A function
with an exact integral representation is absolutely continuous; this covers
continuous functions with an integrable right derivative, such as piecewise
smooth support derivatives with curvature jumps, and almost everywhere their
right derivative is their derivative.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa

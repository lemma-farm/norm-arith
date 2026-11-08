module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.FiniteEnvelope
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Finite spatial first variations and moving-window pressures

The finite envelope theorem differentiates actual min/max wall integrals.
Here it gives the charged exterior-source minus middle-source first
variation, and hence its necessary inequality at a selected maximum.

The separate endpoint calculation retains the motion of both ends of the
middle-half window. Its pressures involve `roof + niche`; they reduce to
one half only at special geometric configurations. These analytic formulas
apply to an actual axis-wall variation only after its positive end face
has been shown to move the actual projection endpoint.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
end AmbidextrousSofa

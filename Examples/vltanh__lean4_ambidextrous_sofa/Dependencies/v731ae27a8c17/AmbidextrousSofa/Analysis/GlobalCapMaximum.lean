module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapMaximum
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapTranslation
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.WideCap
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.Chord
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Reference.Value
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Global existence and canonicalization of full cap maxima

The reference cap supplies a concrete comparison value. Every cap of width
at least six has a strictly smaller score; every narrower cap can be
translated into one fixed compact box. A maximum in that box is therefore
a maximum over the entire original cap domain. The actual chord and height
operations then give a height-one maximizer affine on its middle window.
The sharp value of that maximum is not presumed here.
-/
noncomputable section
open Set
namespace AmbidextrousSofa
end AmbidextrousSofa

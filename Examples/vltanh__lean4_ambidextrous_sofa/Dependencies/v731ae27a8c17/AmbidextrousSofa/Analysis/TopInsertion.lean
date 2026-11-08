module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapInsertion
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.GlobalCapMaximum
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.FiniteScore
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Top insertion preserves the whole barrier on the middle window

When an old height-one point lies to the right of an inserted height-one
point, the first supporting walls are unchanged. Any changed second wall is
nonpositive at every abscissa to the left of the inserted point. Thus the
positive part of every corner, its whole angular supremum, and the whole
partial barrier are unchanged there. For nested caps with the same
projection and the same middle barrier, a strict roof gain at a point of a
charged wing strictly increases the score; so inserting at the right end of
the middle window strictly increases the full-turn score if its old roof is
below one. This is an actual set variation.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa

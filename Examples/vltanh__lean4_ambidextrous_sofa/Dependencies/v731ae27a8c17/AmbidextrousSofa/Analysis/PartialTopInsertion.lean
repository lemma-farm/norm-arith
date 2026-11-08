module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.JointCapMaximum
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.TopInsertion
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Top insertion for both orientations at a proper angle

An existing top point on the left protects every second-wall support, while
each changed first wall, including the whole outgoing terminal wall, is
nonpositive on the middle interval. Together with the insertion from the
right, these are two direct set variations.

In both the whole partial barrier is unchanged on that interval, and the
actual charged roof gains strictly whenever the inserted endpoint was below one.
Thus a height-one joint maximum has a top point in its middle interval.
The high endpoint of any affine middle roof is consequently at height one,
for either sign of its slope.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa

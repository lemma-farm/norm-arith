module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.CapScoreContinuity
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Existence of actual spatial cap maxima in a compact box

The domain consists of every nonempty compact convex downward cap contained
in the indicated compact set. Both degenerate and nonsmooth caps are kept.
Its compactness follows from the geometric Hausdorff limit theorem; the
full spatial score is continuous on this domain by its actual moving-window
integrals. The extreme-value theorem therefore supplies a genuine cap.
-/
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace AmbidextrousSofa
end AmbidextrousSofa

module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreWeakSobolevTruncation
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.RadialSobolevSpace
@[expose] public section
/-! # Spatial approximation in the independent radial weak Sobolev space

Radiality means existence of an almost-everywhere representative depending on
the individual squared radii and invariant under particle permutations. No
smoothness or membership in the smooth-core closure enters this definition.
Every such weak-H¹ pair admits compact radial weak-H¹ approximants.
Smooth approximation is a separate, still required step.
-/
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
end
end GinibrePoincare

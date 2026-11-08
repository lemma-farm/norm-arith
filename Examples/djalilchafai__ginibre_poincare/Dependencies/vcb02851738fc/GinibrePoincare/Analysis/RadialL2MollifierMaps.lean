module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.RadialL2Convolution
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.LebesgueL2MollificationMaps
@[expose] public section
/-! # Linear compatibility of ordinary L² mollification

Continuous linear maps of the values commute with translation and normalized
bump averaging. This permits simultaneous mollification of gradient coordinates.
-/
open MeasureTheory Filter
open scoped Topology Convolution
namespace GinibrePoincare
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
end
end GinibrePoincare

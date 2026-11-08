module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibrePhaseRegularSobolev
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreDensityBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Pi
@[expose] public section
/-! # Local inverse-radius control at simultaneous coordinate zeroes

For distinct complex coordinates the reciprocal of their combined squared radius
is locally Lebesgue integrable. This is the concrete domination needed for cutoff
energy at the remaining exceptional set of the radial weak-domain argument.
-/
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
end
end GinibrePoincare

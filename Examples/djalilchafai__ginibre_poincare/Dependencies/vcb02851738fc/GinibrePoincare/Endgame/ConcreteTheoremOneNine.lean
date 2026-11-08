module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreGeneratorL2
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreConjugationGeometry
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.HermiteWeightedEnergy
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.WeightedSeriesTruncation
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.VandermondeGroundStateZeroMode
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Endgame.FiniteTheoremOneNine
@[expose] public section
/-! # Concrete assembly of the two identities in Theorem 1.9 -/
namespace GinibrePoincare
noncomputable section
open scoped Topology
open MeasureTheory
open ComplexHermite
open Filter
local instance concrete_completeSpace_gaussianAlternatingL2 (n : ℕ) :
    CompleteSpace (gaussianAlternatingL2 n) :=
  (isClosed_gaussianAlternatingL2 n).completeSpace_coe
local instance concrete_completeSpace_ginibreSymmetricL2 (n : ℕ) :
    CompleteSpace (ginibreSymmetricL2 n) :=
  (isClosed_ginibreSymmetricL2 n).completeSpace_coe
end
end GinibrePoincare

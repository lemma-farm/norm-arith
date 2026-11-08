module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.HolomorphicVandermondeDivision
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.HermiteEnergy
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.VandermondeL2Inverse
@[expose] public section
/-! # Closed zero-mode Vandermonde correspondence -/
open MeasureTheory
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section
local instance completeSpace_gaussianAlternatingL2 (n : ℕ) :
    CompleteSpace (gaussianAlternatingL2 n) :=
  (isClosed_gaussianAlternatingL2 n).completeSpace_coe
local instance completeSpace_ginibreSymmetricL2 (n : ℕ) :
    CompleteSpace (ginibreSymmetricL2 n) :=
  (isClosed_ginibreSymmetricL2 n).completeSpace_coe
end
end ComplexHermite
end GinibrePoincare

module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.HolomorphicVandermondeL2Closure
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GlobalPhaseAction
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.L2RepresentativeBridges
@[expose] public section
/-! # Conjugation geometry on symmetric Ginibre L² -/
open MeasureTheory
open scoped ComplexConjugate ENNReal
namespace GinibrePoincare
noncomputable section
local instance completeSpace_gaussianAlternatingL2' (n : ℕ) :
    CompleteSpace (gaussianAlternatingL2 n) :=
  (isClosed_gaussianAlternatingL2 n).completeSpace_coe
local instance completeSpace_ginibreSymmetricL2' (n : ℕ) :
    CompleteSpace (ginibreSymmetricL2 n) :=
  (isClosed_ginibreSymmetricL2 n).completeSpace_coe
end
end GinibrePoincare

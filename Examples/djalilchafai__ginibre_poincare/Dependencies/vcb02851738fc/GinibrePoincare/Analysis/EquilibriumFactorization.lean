module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Concrete.Configuration
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Concrete.CenterOfMass
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Concrete.MeasureModel
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Concrete.Vandermonde
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Concrete.Weights
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Concrete.GroundState
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.ComplexGaussianDensity
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreMassFiniteness
@[expose] public section
/-!
# Equilibrium Factorization (Theorem 1.2)

The geometric decomposition and pointwise density identity of Theorem 1.2.
The normalized density below is identified with the actual `ginibreMeasure`.
The probabilistic independence and Gaussian marginal law are proved in
`EquilibriumProbability.lean`. The recentered-radius Gamma law is proved in
`GinibreRadialGamma.lean`.
-/
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
-- Define the projection operators
def zeroSumHyperplane (n : ℕ) : Submodule ℂ (Configuration n) where
  carrier := {z | coordinateSum z = 0}
  zero_mem' := by simp [coordinateSum]
  add_mem' := by
    intro z w hz hw
    simp only [Set.mem_ofPred_eq, coordinateSum, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [hz, hw, add_zero]
  smul_mem' := by
    intro a z hz
    simp only [Set.mem_ofPred_eq, coordinateSum, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum] at *
    rw [hz, mul_zero]
end
end GinibrePoincare

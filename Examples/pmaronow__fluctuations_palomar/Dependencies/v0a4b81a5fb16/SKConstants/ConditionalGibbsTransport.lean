module
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.ConditionalGibbsConvexity
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.TransportEntropy
public import Mathlib
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal Topology BoundedContinuousFunction
namespace SKConstants
open Transport
def conditionalNormalizedGibbsPotential {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  conditionalGibbsPotential beta sigma x z -
    Real.log ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin n × Fin n) /
      conditionalGibbsSpinMass beta sigma x)
theorem conditionalGibbsGaussianLaw_eq_exp_normalized {n : ℕ}
    (beta sigma : ℝ) (x : Spin n) :
    conditionalGibbsGaussianLaw beta sigma x =
      expPotentialLaw (conditionalNormalizedGibbsPotential beta sigma x) := by
  rw [conditionalGibbsGaussianLaw_eq_exp_potential, expPotentialLaw]
  congr 1
  funext z
  congr 1
  have hc : 0 < (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin n × Fin n) /
      conditionalGibbsSpinMass beta sigma x :=
    div_pos (pow_pos (inv_pos.mpr (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos))) _)
      (conditionalGibbsSpinMass_pos beta sigma x)
  rw [conditionalNormalizedGibbsPotential, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hc]
instance conditionalNormalizedGibbsPotential_isProbability {n : ℕ}
    (beta sigma : ℝ) (x : Spin n) :
    IsProbabilityMeasure (expPotentialLaw (conditionalNormalizedGibbsPotential beta sigma x)) := by
  rw [← conditionalGibbsGaussianLaw_eq_exp_normalized]
  infer_instance
end SKConstants

module
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.HamiltonianDerivativeCovariance
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.FiniteCorrelationIto
set_option autoImplicit false
public section
/-! Actual finite-N coefficient-gradient contractions in the energy
integration-by-parts identity, including the dimension-vanishing rank-one
correction. The covariance tensor is calculated from the real ordered
Hamiltonian; it is not a premise of any theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace
namespace SphericalAging.EnergyCovarianceContraction
open FiniteModel HardSphereDynamics GaussianIntegrationByParts
open HamiltonianDerivativeCovariance FiniteCorrelationIto
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] def normalizedTrace {N : ℕ} (U : Vector N →L[ℝ] Vector N) : ℝ := operatorTrace U/N
lemma operatorTrace_abs_le {N : ℕ} (U : Vector N →L[ℝ] Vector N) :
    |operatorTrace U| ≤ (N : ℝ)*‖U‖ := by
  rw [operatorTrace,LinearMap.trace_eq_sum_inner U.toLinearMap (EuclideanSpace.basisFun (Fin N) ℝ)]
  calc
    _ ≤ ∑ i : Fin N, |inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i)
      (U (EuclideanSpace.basisFun (Fin N) ℝ i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ‖U‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hn : ‖EuclideanSpace.basisFun (Fin N) ℝ i‖=1 :=
        (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.norm_eq_one i
      calc
        _ ≤ ‖EuclideanSpace.basisFun (Fin N) ℝ i‖*‖U (EuclideanSpace.basisFun (Fin N) ℝ i)‖ :=
          norm_inner_le_norm (𝕜 := ℝ) _ _
        _ ≤ ‖EuclideanSpace.basisFun (Fin N) ℝ i‖*(‖U‖*‖EuclideanSpace.basisFun (Fin N) ℝ i‖) := by
          exact mul_le_mul_of_nonneg_left (U.le_opNorm _) (norm_nonneg _)
        _ = _ := by rw [hn]; ring
    _ = _ := by simp
lemma normalizedTrace_abs_le {N : ℕ} (hN : 0 < N) (U : Vector N →L[ℝ] Vector N) :
    |normalizedTrace U| ≤ ‖U‖ := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [normalizedTrace,abs_div,abs_of_pos hn,div_le_iff₀ hn]
  simpa only [mul_comm] using operatorTrace_abs_le U
/-- The genuine signed normalized trace is controlled by the actual
operator norm, even when the response trace changes sign. -/
theorem weighted_trace_replacement_le {N : ℕ} (hN : 0 < N) (n : ℕ)
    {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (U : Vector N →L[ℝ] Vector N) :
    |(a^n-b^n)*normalizedTrace U| ≤ (n : ℝ)*|a-b| *‖U‖ := by
  have hp : |a^n-b^n| ≤ (n : ℝ)*|a-b| := by
    calc
      _ ≤ |a-b| *(n : ℝ)*(max |a| |b|)^(n-1) := abs_pow_sub_pow_le a b n
      _ ≤ |a-b| *(n : ℝ)*1^(n-1) := by gcongr; exact max_le ha hb
      _ = _ := by simp; ring
  rw [abs_mul]
  exact (mul_le_mul hp (normalizedTrace_abs_le hN U) (abs_nonneg _) (by positivity)).trans_eq (by ring)
end SphericalAging.EnergyCovarianceContraction

module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Divisors

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v1cc7829b769f.GuthMaynard.Improvement.PoissonReduction ====
public section
set_option autoImplicit false
@[expose] public section
/-! Exact Fourier/Poisson identities for the unequal-scale reduction.
Quantitative tails and divisor-counting estimates are separate obligations.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped FourierTransform
namespace GuthMaynard.Improvement
def phase (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

end GuthMaynard.Improvement

end
end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v1cc7829b769f.GuthMaynard.Improvement.PoissonTails ====
public section
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement

def poissonRemainder (ψ : ℝ → ℂ) (R α H : ℝ) (n : ℤ) : ℂ :=
  if H < |R*((n:ℝ)-α)| then 𝓕 ψ (R*((n:ℝ)-α)) else 0

end GuthMaynard.Improvement

end
end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_4cb575b6d743389767f1_SecondKernelError ====
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement

def secondKernelError (ψ : ℝ → ℂ) (S K H τ : ℝ) (Q : Finset ℝ) (z : ℝ × ℝ) : ℂ :=
  ∑ q ∈ Q, ∑ q' ∈ Q, ((q*q':ℝ):ℂ)*phase (τ*(q'*z.2-q*z.1))*
    (((S/K:ℝ):ℂ)*(∑' n : ℤ, poissonRemainder ψ (S/K) (q'*z.2-q*z.1) H n))

set_option linter.unusedVariables false in
/-- Both coefficient sums and the modulus-one oscillatory phase are retained.
The bound is uniform in tau and covers S/K arbitrarily small. -/
theorem second_kernel_error_bound (ψ : 𝓢(ℝ, ℂ)) (j : ℕ) 
    (h_GuthMaynard_Improvement_second_poisson_remainder_bound : ∀ (ψ : SchwartzMap ℝ ℂ) (j : ℕ),
      ∃ (C : ℝ),
        0 ≤ C ∧
          ∀ (S K q q' u u' H : ℝ),
            0 < S →
              0 < K →
                0 ≤ H →
                  ‖(↑(S / K) : ℂ) *
                        ∑' (n : ℤ),
                          GuthMaynard.Improvement.poissonRemainder (⇑ψ : ℝ → ℂ) (S / K)
                            (q' * u' - q * u) H n‖ ≤
                    C * (S / K) * (1 + K / S) ^ 2 / (1 + H) ^ j)
    (h_GuthMaynard_Improvement_phase_norm : ∀ (t : ℝ), ‖GuthMaynard.Improvement.phase t‖ = 1)
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S K H τ : ℝ) (Q : Finset ℝ),
      0 < S → 0 < K → 0 ≤ H → ∀ z : ℝ × ℝ,
      ‖secondKernelError ψ S K H τ Q z‖ ≤
        (C*(S/K)*(1+K/S)^2/(1+H)^j)*(∑ q ∈ Q, |q|)^2 := by
  obtain ⟨C,hC,h⟩ := h_GuthMaynard_Improvement_second_poisson_remainder_bound ψ j
  refine ⟨C,hC,?_⟩
  intro S K H τ Q hS hK hH z
  unfold secondKernelError
  calc
    _ ≤ ∑ q ∈ Q, ∑ q' ∈ Q, ‖((q*q':ℝ):ℂ)*phase (τ*(q'*z.2-q*z.1))*
      (((S/K:ℝ):ℂ)*(∑' n : ℤ, poissonRemainder ψ (S/K) (q'*z.2-q*z.1) H n))‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun q _ => norm_sum_le _ _))
    _ ≤ ∑ q ∈ Q, ∑ q' ∈ Q, (|q| *|q'|)*(C*(S/K)*(1+K/S)^2/(1+H)^j) := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro q' _
      rw [norm_mul, norm_mul, h_GuthMaynard_Improvement_phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (h S K q q' z.1 z.2 H hS hK hH) (by positivity)
    _ = _ := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
end GuthMaynard.Improvement

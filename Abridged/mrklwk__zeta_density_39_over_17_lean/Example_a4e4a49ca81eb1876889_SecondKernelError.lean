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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v294fb6a38fa4.GuthMaynard.Improvement.PoissonReduction ====
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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v294fb6a38fa4.GuthMaynard.Improvement.PoissonTails ====
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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_a4e4a49ca81eb1876889_SecondKernelError ====
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
/-- Actual product-measure integral of the second discarded kernel.
Integrability is proved by domination; the homogeneous mass squared is exact. -/
theorem second_kernel_integrated_error (ψ : 𝓢(ℝ, ℂ)) (j : ℕ) 
    (h_GuthMaynard_Improvement_second_kernel_error_bound : ∀ (ψ : SchwartzMap ℝ ℂ) (j : ℕ),
      ∃ (C : ℝ),
        0 ≤ C ∧
          ∀ (S K H τ : ℝ) (Q : Finset ℝ),
            0 < S →
              0 < K →
                0 ≤ H →
                  ∀ (z : ℝ × ℝ),
                    ‖GuthMaynard.Improvement.secondKernelError (⇑ψ : ℝ → ℂ) S K H τ Q z‖ ≤
                      C * (S / K) * (1 + K / S) ^ 2 / (1 + H) ^ j * (∑ q ∈ Q, |q|) ^ 2)
    (h_GuthMaynard_Improvement_second_kernel_error_measurable : ∀ (ψ : SchwartzMap ℝ ℂ) (S K H τ : ℝ) (Q : Finset ℝ),
      Measurable (GuthMaynard.Improvement.secondKernelError (⇑ψ : ℝ → ℂ) S K H τ Q))
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ) (S K H τ : ℝ) (Q : Finset ℝ),
      Measurable f → Integrable f → (∀ x, 0 ≤ f x) →
      0 < S → 0 < K → 0 ≤ H →
      Integrable (fun z : ℝ × ℝ => ((f z.1*f z.2:ℝ):ℂ)*secondKernelError ψ S K H τ Q z)
        (volume.prod volume) ∧
      ‖∫ z : ℝ × ℝ, ((f z.1*f z.2:ℝ):ℂ)*secondKernelError ψ S K H τ Q z ∂(volume.prod volume)‖ ≤
        (C*(S/K)*(1+K/S)^2/(1+H)^j)*(∑ q ∈ Q, |q|)^2*(∫ x, f x)^2 := by
  obtain ⟨C,hC,h⟩ := h_GuthMaynard_Improvement_second_kernel_error_bound ψ j
  refine ⟨C,hC,?_⟩
  intro f S K H τ Q hfm hfi hf0 hS hK hH
  let D := (C*(S/K)*(1+K/S)^2/(1+H)^j)*(∑ q ∈ Q, |q|)^2
  have hm := h_GuthMaynard_Improvement_second_kernel_error_measurable ψ S K H τ Q
  have hgm : Measurable (fun z : ℝ × ℝ => ((f z.1*f z.2:ℝ):ℂ)*secondKernelError ψ S K H τ Q z) := by fun_prop
  have hi := (hfi.mul_prod hfi).const_mul D
  have hb (z : ℝ × ℝ) : ‖((f z.1*f z.2:ℝ):ℂ)*secondKernelError ψ S K H τ Q z‖ ≤
      D*(f z.1*f z.2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 _) (hf0 _))]
    exact (mul_le_mul_of_nonneg_left (h S K H τ Q hS hK hH z) (mul_nonneg (hf0 _) (hf0 _))).trans_eq (mul_comm _ _)
  have hgi := hi.mono' hgm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hgi, ?_⟩
  calc
    _ ≤ ∫ z : ℝ × ℝ, ‖((f z.1*f z.2:ℝ):ℂ)*secondKernelError ψ S K H τ Q z‖ ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ × ℝ, D*(f z.1*f z.2) ∂(volume.prod volume) := integral_mono hgi.norm hi hb
    _ = _ := by rw [integral_const_mul, integral_prod_mul]; dsimp [D]; ring
end GuthMaynard.Improvement

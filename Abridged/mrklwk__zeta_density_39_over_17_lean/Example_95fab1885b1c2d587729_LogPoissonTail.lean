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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.vcd03936e450b.MathCollab.Density.Packing ====
public section
@[expose] public section
open Real Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- A single absolute constant for every separated row. -/
def separationMass : ℝ := ∑' z : ℤ, 4/(1+|(z : ℝ)|)^2

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.vcd03936e450b.GuthMaynard.Improvement.PoissonTails ====
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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_95fab1885b1c2d587729_LogPoissonTail ====
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff FourierTransform
namespace GuthMaynard.Improvement
set_option linter.unusedVariables false in
/-- Quantitative lattice tail from a specified Fourier bound. This is the
same shifted-lattice estimate as PoissonTails with its constant explicit. -/
theorem poisson_remainder_of_fourier_bound (ψ : ℝ → ℂ) (j : ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ x : ℝ, (1+|x|)^(j+2)*‖𝓕 ψ x‖ ≤ C) 
    (h_GuthMaynard_Improvement_shifted_lattice_decay : ∀ (α : ℝ),
      (Summable fun (n : ℤ) ↦ 1 / (1 + |(↑n : ℝ) - α|) ^ 2) ∧
        ∑' (n : ℤ), 1 / (1 + |(↑n : ℝ) - α|) ^ 2 ≤ MathCollab.Density.separationMass)
    :
    ∀ R α H : ℝ, 0 < R → 0 ≤ H →
      Summable (fun n : ℤ => ‖poissonRemainder ψ R α H n‖) ∧
      ‖∑' n : ℤ, poissonRemainder ψ R α H n‖ ≤
        (C*MathCollab.Density.separationMass)*(1+R⁻¹)^2/(1+H)^j := by
  intro R α H hR hH
  have hRp : 0 < R := hR
  have hb (n : ℤ) : ‖poissonRemainder ψ R α H n‖ ≤
      (C*(1+R⁻¹)^2/(1+H)^j)*(1/(1+|(n:ℝ)-α|)^2) := by
    unfold poissonRemainder
    split_ifs with hn
    · let t := |R*((n:ℝ)-α)|
      have ht0 : 0 ≤ t := abs_nonneg _
      have he : R⁻¹*t = |(n:ℝ)-α| := by
        dsimp [t]
        rw [abs_mul, abs_of_pos hRp, ← mul_assoc, inv_mul_cancel₀ hRp.ne', one_mul]
      have ht : 1+|(n:ℝ)-α| ≤ (1+R⁻¹)*(1+t) := by
        have hr0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hRp.le
        nlinarith
      have hp : (1+H)^j*(1+|(n:ℝ)-α|)^2 ≤ (1+R⁻¹)^2*(1+t)^(j+2) := by
        have h1 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+H)
          (by dsimp [t]; linarith : 1+H ≤ 1+t) j
        have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|(n:ℝ)-α|) ht 2
        have hh := mul_le_mul h1 h2 (by positivity) (by positivity)
        simpa only [pow_add, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hh
      have hh := (mul_le_mul_of_nonneg_right hp
        (norm_nonneg (𝓕 ψ (R*((n:ℝ)-α))))).trans (by
          have hh := mul_le_mul_of_nonneg_left (hc (R*((n:ℝ)-α))) (sq_nonneg (1+R⁻¹))
          simpa only [mul_assoc] using hh)
      have hh' : ‖𝓕 ψ (R*((n:ℝ)-α))‖ ≤ (C*(1+R⁻¹)^2)/((1+H)^j*(1+|(n:ℝ)-α|)^2) :=
        (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hh)
      simpa only [div_mul_div_comm, mul_one] using hh'
    · simp only [norm_zero]
      positivity
  obtain ⟨hs, hsum⟩ := h_GuthMaynard_Improvement_shifted_lattice_decay α
  have hm := hs.mul_left (C*(1+R⁻¹)^2/(1+H)^j)
  have hi := hm.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∑' n : ℤ, ‖poissonRemainder ψ R α H n‖ := norm_tsum_le_tsum_norm hi
    _ ≤ ∑' n : ℤ, (C*(1+R⁻¹)^2/(1+H)^j)*(1/(1+|(n:ℝ)-α|)^2) := hi.tsum_le_tsum hb hm
    _ = (C*(1+R⁻¹)^2/(1+H)^j)*(∑' n : ℤ, 1/(1+|(n:ℝ)-α|)^2) := tsum_mul_left
    _ ≤ (C*(1+R⁻¹)^2/(1+H)^j)*MathCollab.Density.separationMass :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring
end GuthMaynard.Improvement

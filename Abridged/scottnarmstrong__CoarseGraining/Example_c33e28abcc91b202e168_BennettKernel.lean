import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod

-- ==== Examples.scottnarmstrong__CoarseGraining.Dependencies.v1fccab2d7cf0.Homogenization.Probability.IndependentSums.Rosenthal.BennettFunction ====
section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
namespace Homogenization
namespace IndependentSums
open MeasureTheory ProbabilityTheory
open Set
open scoped Topology
noncomputable section
variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}
/-- The Bennett function `h(r) = (1 + r) log (1 + r) - r`. -/
noncomputable def bennettH (r : ℝ) : ℝ :=
  (1 + r) * Real.log (1 + r) - r
/-- The Bennett quotient `β(r) = h(r) / r` on `(0, ∞)`. -/
noncomputable def bennettBeta (r : ℝ) : ℝ :=
  bennettH r / r

end
end IndependentSums
end Homogenization

end

-- ==== Examples.scottnarmstrong__CoarseGraining.Examples.Example_c33e28abcc91b202e168_BennettKernel ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
namespace Homogenization
namespace IndependentSums
open MeasureTheory ProbabilityTheory
open Set
open scoped Topology
noncomputable section
variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- A universal bound for the Bennett kernel integral appearing in the
tail-integration step of Rosenthal's inequality. -/
noncomputable def rosenthalBennettIntegralConst : ℝ :=
  4 * Real.exp 2


set_option linter.unusedVariables false in
/-- After the moment-adapted truncation choice, the Bennett tail integral at
variance scale `σ²` is exactly a scaled copy of the universal Bennett kernel
integral. -/
theorem rosenthal_bennett_scaled_integral_le
    {p sigmaSq : ℝ} (hp : 2 ≤ p) (hSigma_pos : 0 < sigmaSq) 
    (h_Homogenization_IndependentSums_rosenthal_bennett_kernel_integral_le : ∀ {p : ℝ},
      2 ≤ p →
        p *
            ∫ (r : ℝ) in Set.Ioi 0,
              r ^ (p - 1) * Real.exp (-(p * Homogenization.IndependentSums.bennettBeta (r ^ 2))) ≤
          Homogenization.IndependentSums.rosenthalBennettIntegralConst ^ p)
    :
    p * ∫ t in Set.Ioi (0 : ℝ),
      t ^ (p - 1) *
        Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq)))) ≤
          (rosenthalBennettIntegralConst * (Real.sqrt p * Real.sqrt sigmaSq)) ^ p := by
  let b : ℝ := Real.sqrt p * Real.sqrt sigmaSq
  let g : ℝ → ℝ := fun r =>
    r ^ (p - 1) * Real.exp (-(p * bennettBeta (r ^ (2 : ℕ))))
  let f : ℝ → ℝ := fun t =>
    t ^ (p - 1) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ) / (p * sigmaSq))))
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_two hp
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have hb_pos : 0 < b := by
    dsimp [b]
    exact mul_pos (Real.sqrt_pos.2 hp_pos) (Real.sqrt_pos.2 hSigma_pos)
  have hb_nonneg : 0 ≤ b := hb_pos.le
  have hb_sq : b ^ (2 : ℕ) = p * sigmaSq := by
    dsimp [b]
    rw [pow_two]
    nlinarith [Real.sq_sqrt hp_nonneg, Real.sq_sqrt hSigma_pos.le]
  have hcomp :
      ∫ t in Set.Ioi (0 : ℝ), f (b * t) =
        ∫ t in Set.Ioi (0 : ℝ), b ^ (p - 1) * g t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.le
    have harg : (b * t) ^ (2 : ℕ) / (p * sigmaSq) = t ^ (2 : ℕ) := by
      calc
        (b * t) ^ (2 : ℕ) / (p * sigmaSq)
            = (b ^ (2 : ℕ) * t ^ (2 : ℕ)) / (p * sigmaSq) := by
                rw [pow_two, pow_two]
                ring
        _ = t ^ (2 : ℕ) := by
              rw [hb_sq]
              field_simp [hp_pos.ne', hSigma_pos.ne']
    calc
      f (b * t)
          = (b * t) ^ (p - 1) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ)))) := by
              dsimp [f]
              rw [harg]
      _ = (b ^ (p - 1) * t ^ (p - 1)) * Real.exp (-(p * bennettBeta (t ^ (2 : ℕ)))) := by
              rw [Real.mul_rpow hb_nonneg ht_nonneg]
      _ = b ^ (p - 1) * g t := by
              dsimp [g]
              ring
  have hscale :
      ∫ t in Set.Ioi (0 : ℝ), f t =
        b ^ p * ∫ r in Set.Ioi (0 : ℝ), g r := by
    calc
      ∫ t in Set.Ioi (0 : ℝ), f t
          = b * ∫ t in Set.Ioi (0 : ℝ), f (b * t) := by
              have hmul :
                  b * ∫ t in Set.Ioi (0 : ℝ), f (b * t) = ∫ t in Set.Ioi (0 : ℝ), f t := by
                rw [MeasureTheory.integral_comp_mul_left_Ioi (g := f) (a := (0 : ℝ)) hb_pos]
                simp [smul_eq_mul, hb_pos.ne']
              exact hmul.symm
      _ = b * ∫ t in Set.Ioi (0 : ℝ), b ^ (p - 1) * g t := by rw [hcomp]
      _ = b * (b ^ (p - 1) * ∫ t in Set.Ioi (0 : ℝ), g t) := by
            rw [MeasureTheory.integral_const_mul]
      _ = b ^ p * ∫ r in Set.Ioi (0 : ℝ), g r := by
            have hpow : b * b ^ (p - 1) = b ^ p := by
              simpa [mul_comm] using (Real.rpow_add hb_pos (1 : ℝ) (p - 1)).symm
            calc
              b * (b ^ (p - 1) * ∫ t in Set.Ioi (0 : ℝ), g t)
                  = (b * b ^ (p - 1)) * ∫ t in Set.Ioi (0 : ℝ), g t := by ring
              _ = b ^ p * ∫ r in Set.Ioi (0 : ℝ), g r := by rw [hpow]
  calc
    p * ∫ t in Set.Ioi (0 : ℝ), f t
        = b ^ p * (p * ∫ r in Set.Ioi (0 : ℝ), g r) := by
            rw [hscale]
            ring
    _ ≤ b ^ p * rosenthalBennettIntegralConst ^ p := by
          gcongr
          exact h_Homogenization_IndependentSums_rosenthal_bennett_kernel_integral_le hp
    _ = (rosenthalBennettIntegralConst * b) ^ p := by
          have hC_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
            dsimp [rosenthalBennettIntegralConst]
            positivity
          rw [mul_comm, ← Real.mul_rpow hC_nonneg hb_nonneg]
    _ = (rosenthalBennettIntegralConst * (Real.sqrt p * Real.sqrt sigmaSq)) ^ p := by
          rfl

end
end IndependentSums
end Homogenization

/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.vc3dad815f120.Planarwave.Analysis.SemigroupGeneratorDensity
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.vc3dad815f120.Planarwave.Analysis.SemigroupRescale
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
@[expose] public section
/-!
# The Laplace resolvent of a strongly continuous semigroup

Integration of an exponentially decaying orbit inverts the negative generator. The closed
generator graph justifies passing from finite orbit integrals to the improper integral.
Complex exponential rescaling then gives the resolvent for `Re z > ω`, with the bound
`M / (Re z - ω)`. These are right-half-plane estimates, not yet sectorial estimates.
-/
open Filter MeasureTheory Set Topology
namespace C0Semigroup
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
/-- The operator-norm growth estimate bounds every orbit on nonnegative real time. -/
theorem norm_realOrbit_le_of_exp_bound (S : C0Semigroup ℂ E) {M ω : ℝ}
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t))
    (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖S.realOrbit x t‖ ≤ (M * ‖x‖) * Real.exp (ω * t) := by
  have hb := hbound t.toNNReal
  rw [Real.coe_toNNReal _ ht] at hb
  calc
    ‖S.realOrbit x t‖ ≤ ‖S t.toNNReal‖ * ‖x‖ := (S t.toNNReal).le_opNorm x
    _ ≤ (M * Real.exp (ω * t)) * ‖x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg x)
    _ = _ := by ring
theorem norm_integral_realOrbit_le (S : C0Semigroup ℂ E) {M ω : ℝ} (hω : ω < 0)
    (hbound : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) (x : E) :
    ‖∫ t in Ioi (0 : ℝ), S.realOrbit x t‖ ≤ (M / (-ω)) * ‖x‖ := by
  have hi := (integrableOn_exp_mul_Ioi hω 0).const_mul (M * ‖x‖)
  calc
    ‖∫ t in Ioi (0 : ℝ), S.realOrbit x t‖ ≤
        ∫ t in Ioi (0 : ℝ), (M * ‖x‖) * Real.exp (ω * t) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact S.norm_realOrbit_le_of_exp_bound hbound x ht.le
    _ = (M / (-ω)) * ‖x‖ := by
      rw [integral_const_mul, integral_exp_mul_Ioi hω]
      simp only [mul_zero, Real.exp_zero]
      ring
end
end C0Semigroup

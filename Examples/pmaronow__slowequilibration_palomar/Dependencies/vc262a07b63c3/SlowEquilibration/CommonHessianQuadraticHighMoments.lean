-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vc262a07b63c3.SlowEquilibration.CommonHessianQuadraticNormalizedExponential
set_option autoImplicit false
/-! Genuine every fixed real moment of a centered Gaussian quadratic form,
with the sharp dimension factor sqrt(m) times its spectral weight bound. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
lemma integer_absolute_moment_of_exponential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (r : ℕ)
    (hPos : Integrable (fun x=>Real.exp (f x)) μ)
    (hNeg : Integrable (fun x=>Real.exp (-f x)) μ) :
    Integrable (fun x=>|f x|^r) μ ∧
      (∫ x,|f x|^r ∂μ) ≤ (r.factorial:ℝ)*
        ((∫ x,Real.exp (f x) ∂μ)+(∫ x,Real.exp (-f x) ∂μ)) := by
  have hFact : 0 < (r.factorial:ℝ):=Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hExp (x) : Real.exp |f x| ≤ Real.exp (f x)+Real.exp (-f x) := by
    by_cases hx : 0 ≤ f x
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_neg (lt_of_not_ge hx)]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  have hp (x) : |f x|^r ≤ (r.factorial:ℝ)*(Real.exp (f x)+Real.exp (-f x)) := by
    have hh:=(div_le_iff₀ hFact).mp (Real.pow_div_factorial_le_exp |f x| (abs_nonneg _) r)
    exact hh.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hExp x) hFact.le)
  have hdom:= (hPos.add hNeg).const_mul (r.factorial:ℝ)
  have hi : Integrable (fun x=>|f x|^r) μ :=
    hdom.mono' (hf.abs.pow_const r).aestronglyMeasurable
      (ae_of_all _ (fun x=>by rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)];exact hp x))
  refine ⟨hi,(integral_mono hi hdom hp).trans_eq ?_⟩
  simp only [integral_const_mul,Pi.add_apply]
  rw [integral_add hPos hNeg]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end
end SlowEquilibration.GaussianQuadraticVariance

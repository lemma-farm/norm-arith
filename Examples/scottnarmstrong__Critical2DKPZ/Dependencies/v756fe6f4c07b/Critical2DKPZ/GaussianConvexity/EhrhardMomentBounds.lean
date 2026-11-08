/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v756fe6f4c07b.Critical2DKPZ.GaussianConvexity.FMPComparison
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v756fe6f4c07b.Critical2DKPZ.GaussianConvexity.ScalarDomainBounds
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v756fe6f4c07b.Critical2DKPZ.GaussianConvexity.LogMGFBasic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Ehrhard-type laws satisfy approximate log-normal moment bounds on their finite exponential-moment domain. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
namespace Critical2DKPZ.GaussianConvexity
/-- Normalized Ehrhard laws satisfy the variance bound with its sharp constant two. -/
theorem variance_le_neg_two_mean {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) (hnorm : ∫ x, Real.exp x ∂μ = 1) :
    Var[id; μ] ≤ -2 * ∫ x, x ∂μ := by
  have := hμ.1
  have h0 := EhrhardType.zero_mem_interior_integrableExpSet_of_isEhrhardType hμ hexp
  have h1 : (1 : ℝ) ∈ integrableExpSet id μ := by
    change Integrable (fun x => Real.exp (1 * id x)) μ
    apply hexp.congr
    apply ae_of_all
    intro x
    change Real.exp x = Real.exp (1 * id x)
    rw [one_mul]
    rfl
  have hline := supporting_line_at_zero_on (convexOn_logMGFRatio_of_isEhrhardType hμ hexp)
    (interior_subset h0) (hasDerivAt_logMGFRatio_zero μ id h0) h1
  rw [logMGFRatio_id_zero, logMGFRatio_id_one_of_normalized μ hnorm, mul_one] at hline
  linarith only [hline]
/-- Every nonnegative negative-moment order satisfies the sharp quadratic logarithmic bound. -/
theorem log_negative_moment_le {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) {p : ℝ} (hp : 0 ≤ p) :
    Real.log (∫ x, Real.exp (-p * x) ∂μ) ≤
      -p * (∫ x, x ∂μ) + p ^ 2 / 2 * Var[id; μ] := by
  have := hμ.1
  have h0 := EhrhardType.zero_mem_interior_integrableExpSet_of_isEhrhardType hμ hexp
  have hneg : -p ∈ integrableExpSet id μ :=
    EhrhardType.integrable_exp_mul_of_isEhrhardType hμ (neg_nonpos.mpr hp)
  have hline := supporting_line_at_zero_on (convexOn_logMGFRatio_of_isEhrhardType hμ hexp)
    (interior_subset h0) (hasDerivAt_logMGFRatio_zero μ id h0) hneg
  have hmul := mul_le_mul_of_nonpos_left hline (neg_nonpos.mpr hp)
  rw [mul_logMGFRatio, logMGFRatio_id_zero] at hmul
  change Real.log (mgf id μ (-p)) ≤ _
  calc
    Real.log (mgf id μ (-p)) ≤ -p * ((∫ x, x ∂μ) + Var[id; μ] / 2 * -p) := hmul
    _ = _ := by ring
end Critical2DKPZ.GaussianConvexity

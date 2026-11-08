/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v4cb506007089.FroehlichSpencer.BKT.Generic.Moment.Taylor
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v4cb506007089.FroehlichSpencer.BKT.Clock.Periodic.ClockWeight
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The per-factor Taylor step for a locally analytic weight

The generic T1.5 per-factor Taylor bound `one_add_mul_lineFactor_ge` (FS81 (6.30)–(6.37);
`Generic/Moment/Taylor.lean`, `Generic/LocalFactorBounds.lean`) is stated for `IsStripWeight`. Its
proof uses only the local strip clauses: analyticity on the strip, the ratio bound, the cost
normalization and nonvanishing on the real axis. The integrable real-line majorant of
`IsStripWeight` is never used. That majorant fails for the periodic clock weight
`exp(β cos(z/N))`.

This file packages the local clauses as `IsLocalStripWeight` and proves that the clock weight
satisfies them (`clockEdgeWeight_isLocalStripWeight`). It then repeats the generic derivative
bounds and the Taylor step verbatim under the weaker hypothesis (suffix `_loc`):
* `genericLocalF_bounds_loc`, `lineFactor_derivs_loc`;
* **`one_add_mul_lineFactor_ge_loc`**: `(1 + z f(0)) exp(z f'(0)/(1 + z f(0)) − err) ≤ 1 + z f(1)`.
-/
@[expose] public section
noncomputable section
namespace FroehlichSpencer.BKT.Clock.Disorder
open Complex
open scoped Real
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Clock.Periodic
variable {ι : Type*}
/-- The local clauses of a strip weight: those used by the T1.5 per-factor Taylor step. -/
structure IsLocalStripWeight (w : ℂ → ℂ) (W : ℝ) (c : ℝ → ℝ) : Prop where
  width_nonneg : 0 ≤ W
  ofReal_ne_zero : ∀ x : ℝ, w x ≠ 0
  analyticAt : ∀ z : ℂ, |z.im| ≤ W → AnalyticAt ℂ w z
  even : ∀ z : ℂ, |z.im| ≤ W → w (-z) = w z
  conj : ∀ z : ℂ, |z.im| ≤ W → (starRingEnd ℂ) (w z) = w ((starRingEnd ℂ) z)
  ratio_le : ∀ t u : ℝ, |u| ≤ W → ‖w ((t : ℂ) + (u : ℂ) * I) / w t‖ ≤ Real.exp (c u)
  cost_even : ∀ u, c (-u) = c u
  cost_zero : c 0 = 0
/-- **The clock weight satisfies the local strip clauses** at every width. -/
theorem clockEdgeWeight_isLocalStripWeight {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hW : 0 ≤ W) :
    IsLocalStripWeight (clockEdgeWeight β n) W (clockShiftCost β n) := by
  have h := clockEdgeWeight_isCompactPeriodicWeight hβ hn
  exact ⟨hW, fun x => h.nonzero x, fun z _ => h.analyticAt z, fun z _ => h.even z,
    fun z _ => h.conj z, fun t u _ => h.ratio_le t u, h.cost_even, h.cost_zero⟩
section Calculus
variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}
/-- The line derivative of a normalized edge factor. -/
theorem hasDerivAt_normalizedEdgeFactor_line_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {a x θ μ₀ : ℝ} (ha : |a| ≤ W) :
    HasDerivAt (fun μ : ℝ => normalizedEdgeFactor w c a (x + μ * θ))
      ((θ : ℂ) * factorLogDeriv w a ((x : ℂ) + (μ₀ : ℂ) * θ) *
        normalizedEdgeFactor w c a (x + μ₀ * θ)) μ₀ := by
  let f : ℂ → ℂ := fun z =>
    w (z + (a : ℂ) * I) / w z * Complex.exp (-((c a : ℝ) : ℂ))
  let z₀ : ℂ := (x : ℂ) + (μ₀ : ℂ) * θ
  have hz₀ : |z₀.im| ≤ W := by
    rw [show z₀.im = 0 by simp [z₀], abs_zero]
    exact hw.width_nonneg
  have hza : |(z₀ + (a : ℂ) * I).im| ≤ W := by
    calc |(z₀ + (a : ℂ) * I).im| = |a| := by simp [z₀]
      _ ≤ W := ha
  have hnum := (hw.analyticAt (z₀ + (a : ℂ) * I) hza).differentiableAt.hasDerivAt
  have hden := (hw.analyticAt z₀ hz₀).differentiableAt.hasDerivAt
  have hnum' := HasDerivAt.comp_add_const z₀ ((a : ℂ) * I) hnum
  have hquot := hnum'.div hden (hnzero z₀ hz₀)
  let dquot : ℂ :=
    (deriv w (z₀ + (a : ℂ) * I) * w z₀ - w (z₀ + (a : ℂ) * I) * deriv w z₀) / w z₀ ^ 2
  have hfun : HasDerivAt f (dquot * Complex.exp (-((c a : ℝ) : ℂ))) z₀ := by
    have h := hquot.mul_const (Complex.exp (-((c a : ℝ) : ℂ)))
    simpa [f, dquot] using h
  have hline := hasDerivAt_realLine hfun
  have hlineEq : (fun μ : ℝ => normalizedEdgeFactor w c a (x + μ * θ)) =
      fun μ : ℝ => f ((x : ℂ) + (μ : ℂ) * θ) := by
    funext μ
    simp [normalizedEdgeFactor, f]
  have hz₀eq : z₀ = ((x + μ₀ * θ : ℝ) : ℂ) := by
    dsimp [z₀]
    push_cast
    ring
  have hderivEq :
      (θ : ℂ) * (dquot * Complex.exp (-((c a : ℝ) : ℂ))) =
        (θ : ℂ) * factorLogDeriv w a z₀ * normalizedEdgeFactor w c a
          (x + μ₀ * θ) := by
    simp only [factorLogDeriv, normalizedEdgeFactor, logDeriv_apply]
    rw [← hz₀eq]
    simp only [dquot]
    field_simp [hnzero z₀ hz₀, hnzero (z₀ + (a : ℂ) * I) hza]
  rw [← hlineEq] at hline
  rw [hderivEq] at hline
  simpa [z₀] using hline
end Calculus
section Bounds
variable {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ} [DecidableEq ι]
omit [DecidableEq ι] in
/-- The normalized edge factor has norm at most one by the strip ratio bound. -/
theorem norm_normalizedEdgeFactor_le_one_loc
    (hw : IsLocalStripWeight w W c) {a x : ℝ} (ha : |a| ≤ W) :
    ‖normalizedEdgeFactor w c a x‖ ≤ 1 := by
  unfold normalizedEdgeFactor
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  calc ‖w ((x : ℂ) + (a : ℂ) * I) / w x‖ * Real.exp (-c a)
      ≤ Real.exp (c a) * Real.exp (-c a) := by
        exact mul_le_mul_of_nonneg_right (hw.ratio_le x a ha) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
omit [DecidableEq ι] in
/-- A product of normalized edge factors has norm at most one. -/
theorem norm_genericEdgeProduct_le_one_loc
    (hw : IsLocalStripWeight w W c) {S : Finset ι} (a x θ : ι → ℝ) (μ : ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) :
    ‖genericEdgeProduct w c S a x θ μ‖ ≤ 1 := by
  unfold genericEdgeProduct
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun e he => norm_nonneg _)
    (fun e he => norm_normalizedEdgeFactor_le_one_loc hw (ha e he))
/-- A finite product rule using the logarithmic derivative of each normalized edge factor. -/
theorem hasDerivAt_genericEdgeProduct_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (genericEdgeProduct w c S a x θ)
      (genericEdgeLogDeriv w S a x θ μ₀ * genericEdgeProduct w c S a x θ μ₀) μ₀ := by
  have hprod := hasDerivAt_product_of_logDeriv
    (f := fun e μ => normalizedEdgeFactor w c (a e) (x e + μ * θ e))
    (q := fun e μ => (θ e : ℂ) *
      factorLogDeriv w (a e) ((x e : ℂ) + (μ : ℂ) * θ e)) μ₀
    (fun e he => hasDerivAt_normalizedEdgeFactor_line_loc hw hnzero
      (a := a e) (x := x e) (θ := θ e) (μ₀ := μ₀) (ha e he))
  change HasDerivAt
    (fun μ => ∏ e ∈ S, normalizedEdgeFactor w c (a e) (x e + μ * θ e))
    ((∑ e ∈ S, (θ e : ℂ) * factorLogDeriv w (a e)
      ((x e : ℂ) + (μ₀ : ℂ) * θ e)) *
        ∏ e ∈ S, normalizedEdgeFactor w c (a e) (x e + μ₀ * θ e)) μ₀
  exact hprod
/-- The derivative of the finite product is its log-derivative sum times the product. -/
theorem deriv_genericEdgeProduct_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) :
    deriv (genericEdgeProduct w c S a x θ) =
      fun μ => genericEdgeLogDeriv w S a x θ μ * genericEdgeProduct w c S a x θ μ := by
  funext μ
  exact (hasDerivAt_genericEdgeProduct_loc hw hnzero a x θ ha μ).deriv
omit [DecidableEq ι] in
/-- The product log-derivative varies with derivative `genericEdgeLogDeriv2`. -/
theorem hasDerivAt_genericEdgeLogDeriv_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (genericEdgeLogDeriv w S a x θ)
      (genericEdgeLogDeriv2 w S a x θ μ₀) μ₀ := by
  unfold genericEdgeLogDeriv genericEdgeLogDeriv2
  refine HasDerivAt.fun_sum fun e he => ?_
  have h := hasDerivAt_factorLogDeriv_line
    (fun z hz => hw.analyticAt z hz) hnzero
    (a := a e) (x := x e) (θ := θ e) (μ₀ := μ₀) (ha e he) hw.width_nonneg
  have h' := h.const_mul (θ e : ℂ)
  convert h' using 1
  ring
/-- The second derivative of the finite product. -/
theorem hasDerivAt_deriv_genericEdgeProduct_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {S : Finset ι} (a x θ : ι → ℝ)
    (ha : ∀ e ∈ S, |a e| ≤ W) (μ₀ : ℝ) :
    HasDerivAt (deriv (genericEdgeProduct w c S a x θ))
      ((genericEdgeLogDeriv w S a x θ μ₀ ^ 2 +
        genericEdgeLogDeriv2 w S a x θ μ₀) *
          genericEdgeProduct w c S a x θ μ₀) μ₀ := by
  rw [deriv_genericEdgeProduct_loc hw hnzero a x θ ha]
  have h := (hasDerivAt_genericEdgeLogDeriv_loc hw hnzero a x θ ha μ₀).mul
    (hasDerivAt_genericEdgeProduct_loc hw hnzero a x θ ha μ₀)
  convert h using 1
  ring
/-- One generic finite product and its first two line derivatives. -/
theorem genericEdgeProduct_bounds_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    (hlog : HasLogDerivBounds w W M)
    {S : Finset ι} (a x θ : ι → ℝ) (A T m μ : ℝ)
    (haA : ∀ e ∈ S, |a e| ≤ A) (hAW : A ≤ W)
    (hθT : ∀ e ∈ S, |θ e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) :
    ‖genericEdgeProduct w c S a x θ μ‖ ≤ 1 ∧
      ‖deriv (genericEdgeProduct w c S a x θ) μ‖ ≤ S.card * m * T ∧
      ‖deriv (deriv (genericEdgeProduct w c S a x θ)) μ‖ ≤
        2 * S.card ^ 2 * m * T ^ 2 := by
  have haW : ∀ e ∈ S, |a e| ≤ W := fun e he => (haA e he).trans hAW
  have hP := norm_genericEdgeProduct_le_one_loc hw a x θ μ haW
  have hQ := norm_genericEdgeLogDeriv_bounds hlog a x θ A T m μ haA hAW hθT hM
  have hderiv : ‖deriv (genericEdgeProduct w c S a x θ) μ‖ ≤ S.card * m * T := by
    rw [deriv_genericEdgeProduct_loc hw hnzero a x θ haW, norm_mul]
    calc ‖genericEdgeLogDeriv w S a x θ μ‖ *
          ‖genericEdgeProduct w c S a x θ μ‖ ≤ (S.card * m * T) * 1 :=
        mul_le_mul hQ.1 hP (norm_nonneg _) ((norm_nonneg _).trans hQ.1)
      _ = S.card * m * T := mul_one _
  have hderiv2 :
      ‖deriv (deriv (genericEdgeProduct w c S a x θ)) μ‖ ≤
        2 * S.card ^ 2 * m * T ^ 2 := by
    rw [(hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero a x θ haW μ).deriv, norm_mul]
    have hsq : ‖genericEdgeLogDeriv w S a x θ μ‖ ^ 2 ≤
        (S.card * m * T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hQ.1 2
    have hNN : (S.card : ℝ) ≤ S.card ^ 2 := by
      rcases Nat.eq_zero_or_pos S.card with h0 | hpos
      · rw [h0]
        norm_num
      · have : (1 : ℝ) ≤ S.card := by exact_mod_cast hpos
        nlinarith
    have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
    have hM2 : m ^ 2 ≤ m := by nlinarith
    have hsum :
        ‖genericEdgeLogDeriv w S a x θ μ ^ 2 +
          genericEdgeLogDeriv2 w S a x θ μ‖ ≤
            (S.card * m * T) ^ 2 + S.card * m * T ^ 2 := by
      calc _ ≤ ‖genericEdgeLogDeriv w S a x θ μ‖ ^ 2 +
            ‖genericEdgeLogDeriv2 w S a x θ μ‖ := by
              refine (norm_add_le _ _).trans ?_
              rw [norm_pow]
        _ ≤ _ := add_le_add hsq hQ.2
    have hkey : (S.card * m * T) ^ 2 + S.card * m * T ^ 2 ≤
        2 * S.card ^ 2 * m * T ^ 2 := by
      have h1 : (S.card * m * T) ^ 2 = S.card ^ 2 * T ^ 2 * m ^ 2 := by ring
      have h2 : S.card ^ 2 * T ^ 2 * m ^ 2 ≤ S.card ^ 2 * T ^ 2 * m :=
        mul_le_mul_of_nonneg_left hM2 (by positivity)
      have h3 : S.card * m * T ^ 2 ≤ S.card ^ 2 * m * T ^ 2 := by
        have := mul_le_mul_of_nonneg_right hNN (mul_nonneg hm0 hT2)
        nlinarith [this]
      nlinarith
    calc
      ‖genericEdgeLogDeriv w S a x θ μ ^ 2 +
          genericEdgeLogDeriv2 w S a x θ μ‖ *
          ‖genericEdgeProduct w c S a x θ μ‖ ≤
        ((S.card * m * T) ^ 2 + S.card * m * T ^ 2) * 1 :=
          mul_le_mul hsum hP (norm_nonneg _) (by positivity)
      _ ≤ 2 * S.card ^ 2 * m * T ^ 2 := by rw [mul_one]; exact hkey
  exact ⟨hP, hderiv, hderiv2⟩
end Bounds
section LocalFunctionals
end LocalFunctionals
end FroehlichSpencer.BKT.Clock.Disorder
end

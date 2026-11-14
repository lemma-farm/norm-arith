import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Examples.Example_3089819004377de562e6_Gevrey ====
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Taper/Gevrey.lean — Gevrey-class taper profiles (items P1–P4 below).

PURPOSE.  The family / q-aspect version of the theorem (paper rem:otherL (iii): "requires a different (Gevrey-class)
taper in prop:tail") needs a profile ϱ with sup|ϱ^{(k)}| ≤ B·A^k·k^{sk} (all k ≥ 1) for some s > 1.  We fix s = 2 and the
explicit profile built from Mathlib's Real.expNegInvGlue g(x) = exp(−1/x) (x>0), 0 (x≤0):
   θ(x) := g(x)·g(1−x)   (a bump on (0,1)),      ϱ₂(x) := (∫_0^x θ) / (∫_0^1 θ).
CONTENTS (all tools exist in Mathlib):
 (P1) gevrey_expNegInvGlue : ∀ k ≥ 1, ∀ x, |iteratedDeriv k expNegInvGlue x| ≤ (18/e)^k · k^(2k).
      Route: for x > 0, expNegInvGlue =ᶠ[𝓝 x] (fun t => (G t).re) with G z := Complex.exp (−1/z) holomorphic on ℂ∖{0};
      real/complex iterated derivatives agree (induction with HasDerivAt.real_of_complex + EventuallyEq.iteratedDeriv_eq);
      Cauchy's estimate Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le on the circle |z − x| = x/2, where
      Re(1/z) = Re z/|z|² ≥ 2/(9x) so ‖G z‖ ≤ exp(−2/(9x)); then k!·(x/2)^{−k}·exp(−2/(9x)) ≤ k!·(9k/e)^k ≤ (9/e)^k k^{2k}·(k!/k^k)
      (sup_t t^k e^{−2t/9} = (9k/(2e))^k).  For x < 0 all derivatives vanish (eventually 0); x = 0 by continuity of
      iteratedDeriv k (expNegInvGlue is C^∞: Real.expNegInvGlue.contDiff).
 (P2) gevrey_mul : Leibniz (norm_iteratedFDeriv_mul_le / iteratedDeriv version): (G_s) for f,h with (A,B) ⇒ (G_s) for f·h
      with (2A, B²), using j^{sj}(k−j)^{s(k−j)} ≤ k^{sk} and Σ_j C(k,j) = 2^k.
 (P3) theta, rhoTwo : definitions; rhoTwo is a TaperProfile (monotone: θ ≥ 0; = 0 / = 1 outside (0,1); C^∞, indeed C³ as
      TaperProfile wants) and iteratedDeriv (k+1) rhoTwo = iteratedDeriv k θ / ∫θ.
 (P4) gevreyProfile_rhoTwo : GevreyProfile 2 (36/e) (2·e^8) rhoTwo   (∫_0^1 θ ≥ e^{−8}/2 since θ ≥ e^{−8} on [1/4,3/4]).
Downstream: a Gevrey tail lemma gives TailInputs with
θ₀ = η/L once (wD₀/A)^{1/2} ≥ c₁^{−1}[L/2 + log d + …]; nothing else in §2.2/§4 changes (c_ϱ finite).
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
noncomputable section
namespace Zeta23
namespace Taper
open Real Complex Filter Topology Set Metric MeasureTheory intervalIntegral
def theta (x : ℝ) : ℝ := expNegInvGlue x * expNegInvGlue (1 - x)
namespace Gevrey2

end Gevrey2

/-! ### bounds for g and g(1−·) with the convention gb 0 = 1 -/
def gb (k : ℕ) : ℝ := (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)

/-! ### θ -/
set_option linter.unusedVariables false in
/-- Leibniz ⇒ |θ^{(k)}| ≤ (36/e)^k k^{2k}. -/
lemma abs_iteratedDeriv_theta_le (k : ℕ) (x : ℝ) 
    (h_Zeta23_Taper_gb_mul_gb_le : ∀ {k i : ℕ},
      i ≤ k → Zeta23.Taper.gb i * Zeta23.Taper.gb (k - i) ≤ (18 / Real.exp 1) ^ k * (↑k : ℝ) ^ (2 * k))
    (h_Zeta23_Taper_abs_iteratedDeriv_gflip_le : ∀ (k : ℕ) (x : ℝ), |iteratedDeriv k (fun (t : ℝ) ↦ expNegInvGlue (1 - t)) x| ≤ Zeta23.Taper.gb k)
    (h_Zeta23_Taper_abs_iteratedDeriv_g_le : ∀ (k : ℕ) (x : ℝ), |iteratedDeriv k expNegInvGlue x| ≤ Zeta23.Taper.gb k)
    :
    |iteratedDeriv k theta x| ≤ (36 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
  have hf : ContDiff ℝ k expNegInvGlue := expNegInvGlue.contDiff
  have hg : ContDiff ℝ k (fun t => expNegInvGlue (1 - t)) :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  have h := norm_iteratedFDeriv_mul_le hf hg x (n := k) le_rfl
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
  change |iteratedDeriv k theta x| ≤ _ at h
  refine h.trans ?_
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |iteratedDeriv i expNegInvGlue x|
        * |iteratedDeriv (k - i) (fun t => expNegInvGlue (1 - t)) x|
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ((18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        calc |iteratedDeriv i expNegInvGlue x| * |iteratedDeriv (k - i) (fun t => expNegInvGlue (1 - t)) x|
            ≤ gb i * gb (k - i) := mul_le_mul (h_Zeta23_Taper_abs_iteratedDeriv_g_le i x) (h_Zeta23_Taper_abs_iteratedDeriv_gflip_le _ x)
                (abs_nonneg _) (by unfold gb; positivity)
          _ ≤ _ := h_Zeta23_Taper_gb_mul_gb_le hik
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * ((18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)) := by
        rw [Finset.sum_mul]
    _ = (2:ℝ) ^ k * ((18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)) := by
        congr 1; exact_mod_cast Nat.sum_range_choose k
    _ = (36 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
        rw [← mul_assoc, ← mul_pow]; congr 2; ring
/-! ### Θ = primitive of θ -/
end Taper
end Zeta23

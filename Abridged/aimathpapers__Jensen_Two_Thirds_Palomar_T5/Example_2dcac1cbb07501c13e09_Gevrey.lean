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

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Examples.Example_2dcac1cbb07501c13e09_Gevrey ====
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

/-! ### (P1) Gevrey-2 bounds for exp(−1/x) via Cauchy's estimate -/
namespace Gevrey2
/-- holomorphic extension of exp(−1/x). -/
def G (z : ℂ) : ℂ := Complex.exp (-z⁻¹)


set_option linter.unusedVariables false in
/-- Cauchy's estimate for G on the circle |z − x| = x/2. -/
lemma norm_iteratedDeriv_G_le (k : ℕ) {x : ℝ} (hx : 0 < x) 
    (h_Zeta23_Taper_Gevrey2_G_differentiableOn : DifferentiableOn ℂ Zeta23.Taper.Gevrey2.G {z : ℂ | z ≠ 0})
    :
    ‖iteratedDeriv k G (x : ℂ)‖ ≤ k.factorial * Real.exp (-(2 / (9 * x))) / (x / 2) ^ k := by
  have hr : (0 : ℝ) < x / 2 := by positivity
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
  · -- DiffContOnCl on the disc: G is differentiable on the closed disc (which misses 0)
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    refine h_Zeta23_Taper_Gevrey2_G_differentiableOn.mono fun z hz h0 => ?_
    rw [mem_closedBall, h0, dist_comm, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx] at hz
    linarith
  · intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have hre : x / 2 ≤ z.re := by
      have := Complex.abs_re_le_norm (z - x)
      simp at this; rw [hz] at this; rw [abs_le] at this; linarith
    have hnorm : ‖z‖ ≤ 3 * x / 2 := by
      calc ‖z‖ = ‖(z - x) + x‖ := by ring_nf
        _ ≤ ‖z - x‖ + ‖(x : ℂ)‖ := norm_add_le _ _
        _ = 3 * x / 2 := by rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]; ring
    have hz0 : z ≠ 0 := fun h => by rw [h] at hre; simp at hre; linarith
    have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    unfold G
    rw [Complex.norm_exp, neg_re, Complex.inv_re]
    apply Real.exp_le_exp.mpr
    -- −(re/normSq) ≤ −2/(9x)  ⟸  2/(9x) ≤ re/normSq
    have hns' : Complex.normSq z ≤ (3 * x / 2) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) hns]
    nlinarith

end Gevrey2

/-! ### bounds for g and g(1−·) with the convention gb 0 = 1 -/

/-! ### θ -/

/-! ### Θ = primitive of θ -/

/-! ### ϱ₂ -/

end Taper
end Zeta23

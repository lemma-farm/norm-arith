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

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Examples.Example_9c70f45658851c8295ce_Gevrey ====
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

namespace Gevrey2
/-- holomorphic extension of exp(−1/x). -/
def G (z : ℂ) : ℂ := Complex.exp (-z⁻¹)

/-- real restriction. -/
def gR (t : ℝ) : ℝ := (G t).re

end Gevrey2
open Gevrey2 in
set_option linter.unusedVariables false in
/-- **(P1)** Gevrey-2 bound for exp(−1/x): |g^{(k)}(x)| ≤ (18/e)^k k^{2k} for all k ≥ 1 and all real x
(Cauchy's estimate for G(z) = exp(−1/z) on the circle |z − x| = x/2, where ‖G‖ ≤ exp(−2/(9x))). -/
theorem gevrey_expNegInvGlue (k : ℕ) (hk : 1 ≤ k) (x : ℝ) 
    (h_Zeta23_Taper_Gevrey2_expNegInvGlue_eventuallyEq_gR : ∀ {x : ℝ}, 0 < x → expNegInvGlue =ᶠ[nhds x] Zeta23.Taper.Gevrey2.gR)
    (h_Zeta23_Taper_Gevrey2_cauchy_bound_le : ∀ (k : ℕ),
      1 ≤ k →
        ∀ {x : ℝ},
          0 < x →
            (↑k.factorial : ℝ) * Real.exp (-(2 / (9 * x))) / (x / 2) ^ k ≤
              (18 / Real.exp 1) ^ k * (↑k : ℝ) ^ (2 * k))
    (h_Zeta23_Taper_Gevrey2_norm_iteratedDeriv_G_le : ∀ (k : ℕ) {x : ℝ},
      0 < x →
        ‖iteratedDeriv k Zeta23.Taper.Gevrey2.G (↑x : ℂ)‖ ≤
          (↑k.factorial : ℝ) * Real.exp (-(2 / (9 * x))) / (x / 2) ^ k)
    (h_Zeta23_Taper_Gevrey2_gR_iteratedDeriv : ∀ (n : ℕ) (t : ℝ),
      0 < t →
        iteratedDeriv n Zeta23.Taper.Gevrey2.gR t = (iteratedDeriv n Zeta23.Taper.Gevrey2.G (↑t : ℂ)).re)
    :
    |iteratedDeriv k expNegInvGlue x| ≤ (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * (k : ℝ)) := by
  have hrpow : (k : ℝ) ^ (2 * (k : ℝ)) = (k : ℝ) ^ (2 * k) := by
    rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hrpow]
  set C : ℝ := (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) with hC
  have hC0 : 0 ≤ C := by positivity
  -- x > 0
  have hpos : ∀ x : ℝ, 0 < x → |iteratedDeriv k expNegInvGlue x| ≤ C := by
    intro x hx
    rw [(h_Zeta23_Taper_Gevrey2_expNegInvGlue_eventuallyEq_gR hx).iteratedDeriv_eq, h_Zeta23_Taper_Gevrey2_gR_iteratedDeriv k x hx]
    exact (Complex.abs_re_le_norm _).trans ((h_Zeta23_Taper_Gevrey2_norm_iteratedDeriv_G_le k hx).trans (h_Zeta23_Taper_Gevrey2_cauchy_bound_le k hk hx))
  -- x < 0
  have hneg : ∀ x : ℝ, x < 0 → |iteratedDeriv k expNegInvGlue x| ≤ C := by
    intro x hx
    have hev : expNegInvGlue =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with t ht
      exact expNegInvGlue.zero_of_nonpos ht.le
    rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
    simp [hC0, Nat.one_le_iff_ne_zero.mp hk]
  -- x = 0 by closedness + density
  have hcont : Continuous (iteratedDeriv k expNegInvGlue) :=
    expNegInvGlue.contDiff.continuous_iteratedDeriv k (by exact_mod_cast le_top)
  have hclosed : IsClosed {x : ℝ | |iteratedDeriv k expNegInvGlue x| ≤ C} :=
    isClosed_le (continuous_abs.comp hcont) continuous_const
  have hsub : ({0}ᶜ : Set ℝ) ⊆ {x : ℝ | |iteratedDeriv k expNegInvGlue x| ≤ C} := by
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · exact hneg x h
    · exact hpos x h
  have : x ∈ closure ({0}ᶜ : Set ℝ) := by rw [closure_compl_singleton]; trivial
  exact hclosed.closure_subset_iff.mpr hsub this
/-! ### bounds for g and g(1−·) with the convention gb 0 = 1 -/

/-! ### θ -/

/-! ### Θ = primitive of θ -/
end Taper
end Zeta23

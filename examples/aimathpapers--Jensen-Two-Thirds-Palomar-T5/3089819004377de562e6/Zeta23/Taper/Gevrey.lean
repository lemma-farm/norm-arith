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
import Zeta23.Defs
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

noncomputable section

namespace Zeta23
namespace Taper

open Real Complex Filter Topology Set Metric MeasureTheory intervalIntegral

                                                              
                                                                                         
                                                            
                        
                                               
                
               
               
                                                                                         

                                                      
def theta (x : ℝ) : ℝ := expNegInvGlue x * expNegInvGlue (1 - x)

                                    
                                                 

                                                           
                                                                               

                                                                   

namespace Gevrey2

/-- holomorphic extension of exp(−1/x). -/
def G (z : ℂ) : ℂ := Complex.exp (-z⁻¹)

lemma G_differentiableOn : DifferentiableOn ℂ G {z : ℂ | z ≠ 0} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold G
  exact ((differentiableAt_inv_iff.mpr hz).neg).cexp

lemma G_analyticOnNhd : AnalyticOnNhd ℂ G {z : ℂ | z ≠ 0} :=
  G_differentiableOn.analyticOnNhd isOpen_ne

lemma Gn_hasDerivAt (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (iteratedDeriv n G) (iteratedDeriv (n + 1) G z) z := by
  have h := (G_analyticOnNhd.iterated_deriv n) z hz
  rw [iteratedDeriv_succ, iteratedDeriv_eq_iterate]
  exact h.differentiableAt.hasDerivAt

/-- real restriction. -/
def gR (t : ℝ) : ℝ := (G t).re

lemma gR_iteratedDeriv (n : ℕ) : ∀ t : ℝ, 0 < t → iteratedDeriv n gR t = (iteratedDeriv n G t).re := by
  induction n with
  | zero => intro t _; simp [gR]
  | succ n ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n gR =ᶠ[𝓝 t] fun u : ℝ => (iteratedDeriv n G (u : ℂ)).re := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact ih u hu
    rw [hev.deriv_eq]
    have hz : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    exact ((Gn_hasDerivAt n hz).real_of_complex).deriv

lemma expNegInvGlue_eventuallyEq_gR {x : ℝ} (hx : 0 < x) : expNegInvGlue =ᶠ[𝓝 x] gR := by
  filter_upwards [Ioi_mem_nhds hx] with t ht
  have ht' : ¬ t ≤ 0 := not_le.mpr ht
  simp only [expNegInvGlue, ht', if_false, gR, G]
  rw [show -(t : ℂ)⁻¹ = ((-t⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.exp_ofReal_re]

/-- Cauchy's estimate for G on the circle |z − x| = x/2. -/
lemma norm_iteratedDeriv_G_le (k : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv k G (x : ℂ)‖ ≤ k.factorial * Real.exp (-(2 / (9 * x))) / (x / 2) ^ k := by
  have hr : (0 : ℝ) < x / 2 := by positivity
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
  · -- DiffContOnCl on the disc: G is differentiable on the closed disc (which misses 0)
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    refine G_differentiableOn.mono fun z hz h0 => ?_
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

/-- elementary: u^k e^{−u} ≤ (k/e)^k for u ≥ 0, k ≥ 1. -/
lemma pow_mul_exp_neg_le (k : ℕ) (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * Real.exp (-u) ≤ ((k : ℝ) / Real.exp 1) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : u / k ≤ Real.exp (u / k - 1) := by
    have := Real.add_one_le_exp (u / k - 1); linarith
  have h2 : (u / k) ^ k ≤ Real.exp (u / k - 1) ^ k := pow_le_pow_left₀ (by positivity) h1 k
  rw [← Real.exp_nat_mul, show (k : ℝ) * (u / k - 1) = u - k by field_simp] at h2
  rw [div_pow, div_le_iff₀ (by positivity)] at h2
  rw [div_pow, le_div_iff₀ (by positivity), Real.exp_one_pow]
  calc u ^ k * Real.exp (-u) * Real.exp k
      ≤ (Real.exp (u - k) * (k : ℝ) ^ k) * Real.exp (-u) * Real.exp k := by gcongr
    _ = (k : ℝ) ^ k * (Real.exp (u - k) * Real.exp (-u) * Real.exp k) := by ring
    _ = (k : ℝ) ^ k := by
        rw [← Real.exp_add, ← Real.exp_add, show u - k + -u + k = 0 by ring, Real.exp_zero, mul_one]

/-- the numeric step: k!·e^{−2/(9x)}·(x/2)^{−k} ≤ (18/e)^k k^{2k}. -/
lemma cauchy_bound_le (k : ℕ) (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    k.factorial * Real.exp (-(2 / (9 * x))) / (x / 2) ^ k ≤ (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
  set u : ℝ := 2 / (9 * x) with hu
  have hu0 : 0 ≤ u := by positivity
  have hxu : (x / 2)⁻¹ = 9 * u := by rw [hu]; field_simp
  have hkey := pow_mul_exp_neg_le k hk hu0
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  rw [div_eq_mul_inv, ← inv_pow, hxu, mul_pow]
  -- k! * e^{-u} * (9^k u^k) ≤ k^k * 9^k (k/e)^k ≤ (18/e)^k k^{2k}
  have h9 : (0:ℝ) ≤ 9 ^ k := by positivity
  calc (k.factorial : ℝ) * Real.exp (-u) * ((9:ℝ) ^ k * u ^ k)
      = (k.factorial : ℝ) * (9:ℝ) ^ k * (u ^ k * Real.exp (-u)) := by ring
    _ ≤ (k : ℝ) ^ k * (9:ℝ) ^ k * (((k : ℝ) / Real.exp 1) ^ k) := by
        gcongr
    _ = (9 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by rw [div_pow, div_pow, pow_mul]; ring
    _ ≤ (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
        gcongr; norm_num

end Gevrey2

open Gevrey2 in
/-- **(P1)** Gevrey-2 bound for exp(−1/x): |g^{(k)}(x)| ≤ (18/e)^k k^{2k} for all k ≥ 1 and all real x
(Cauchy's estimate for G(z) = exp(−1/z) on the circle |z − x| = x/2, where ‖G‖ ≤ exp(−2/(9x))). -/
theorem gevrey_expNegInvGlue (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    |iteratedDeriv k expNegInvGlue x| ≤ (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * (k : ℝ)) := by
  have hrpow : (k : ℝ) ^ (2 * (k : ℝ)) = (k : ℝ) ^ (2 * k) := by
    rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hrpow]
  set C : ℝ := (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) with hC
  have hC0 : 0 ≤ C := by positivity
  -- x > 0
  have hpos : ∀ x : ℝ, 0 < x → |iteratedDeriv k expNegInvGlue x| ≤ C := by
    intro x hx
    rw [(expNegInvGlue_eventuallyEq_gR hx).iteratedDeriv_eq, gR_iteratedDeriv k x hx]
    exact (Complex.abs_re_le_norm _).trans ((norm_iteratedDeriv_G_le k hx).trans (cauchy_bound_le k hk hx))
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

def gb (k : ℕ) : ℝ := (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)

lemma gb_zero : gb 0 = 1 := by simp [gb]

lemma expNegInvGlue_le_one (x : ℝ) : expNegInvGlue x ≤ 1 := by
  unfold expNegInvGlue
  split_ifs with h
  · norm_num
  · apply Real.exp_le_one_iff.mpr
    have : 0 < x := not_le.mp h
    have := inv_pos.mpr this
    linarith

lemma abs_iteratedDeriv_g_le (k : ℕ) (x : ℝ) : |iteratedDeriv k expNegInvGlue x| ≤ gb k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [iteratedDeriv_zero, gb_zero, abs_of_nonneg (expNegInvGlue.nonneg x)]
    exact expNegInvGlue_le_one x
  · have h := gevrey_expNegInvGlue k hk x
    rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h
    exact h

lemma abs_iteratedDeriv_gflip_le (k : ℕ) (x : ℝ) :
    |iteratedDeriv k (fun t => expNegInvGlue (1 - t)) x| ≤ gb k := by
  rw [iteratedDeriv_comp_const_sub]
  simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_iteratedDeriv_g_le k (1 - x)

lemma gb_mul_gb_le {k i : ℕ} (hi : i ≤ k) : gb i * gb (k - i) ≤ (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
  unfold gb
  have h18 : (0:ℝ) ≤ 18 / Real.exp 1 := by positivity
  have hik : (i : ℝ) ≤ k := by exact_mod_cast hi
  have hki : ((k - i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k i
  calc (18 / Real.exp 1) ^ i * (i : ℝ) ^ (2 * i) * ((18 / Real.exp 1) ^ (k - i) * ((k - i : ℕ) : ℝ) ^ (2 * (k - i)))
      = (18 / Real.exp 1) ^ (i + (k - i)) * ((i : ℝ) ^ (2 * i) * ((k - i : ℕ) : ℝ) ^ (2 * (k - i))) := by
        rw [pow_add]; ring
    _ ≤ (18 / Real.exp 1) ^ k * ((k : ℝ) ^ (2 * i) * (k : ℝ) ^ (2 * (k - i))) := by
        rw [Nat.add_sub_cancel' hi]
        gcongr
    _ = (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
        rw [← pow_add]; congr 2; omega

/-! ### θ -/

                                                     
                                                                                           

                                                                                 

                                                                                                        

                                                                      
                                               

                                                                      
                                                                         

                                                                  
                                                                                

/-- Leibniz ⇒ |θ^{(k)}| ≤ (36/e)^k k^{2k}. -/
lemma abs_iteratedDeriv_theta_le (k : ℕ) (x : ℝ) :
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
            ≤ gb i * gb (k - i) := mul_le_mul (abs_iteratedDeriv_g_le i x) (abs_iteratedDeriv_gflip_le _ x)
                (abs_nonneg _) (by unfold gb; positivity)
          _ ≤ _ := gb_mul_gb_le hik
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * ((18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)) := by
        rw [Finset.sum_mul]
    _ = (2:ℝ) ^ k * ((18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)) := by
        congr 1; exact_mod_cast Nat.sum_range_choose k
    _ = (36 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
        rw [← mul_assoc, ← mul_pow]; congr 2; ring

/-! ### Θ = primitive of θ -/

                                                                
                                                                     
                                                                                   

                                                                                     

                                                                                                     

                                                                     
                                            
                                              

                                                                                                  
                                       

                                                              
              
                                 
                                                           
                                                                                                 
      

                                                                    
              
                                                                                          
                                              
                                                                   
                                                                                                 
      

                                    
                                                                                                            
               

                                                     
                                                      
                             
                                                                      
              
                                                   
                                            
                                                         
                               
                                                                          
                                                         
                                                
                                                         
                               
                                                                          
                                                                                          
                                                                                  
              
                                                                                                           
                                                                                                                    
                                                                                                       
                                                                                                     
                                                                    
                                                                                  
                                                                      
                                                             
            
          

             

                                                                
                                          

                                                                                 

                                                                       
                                                             

                                              
                
                      
                                                                                   
                
                      
                                                                                                                  
                                          
                                                                 
                                                                                         

                                            
                                                                                
                                                                             

                                                                                          
                                                      
                                                                                              
                       
                           
                       
                        
                        
                    
                                                         
                                                                         
                                                
                                                     
                          
                                                                                       
                
                                             
                                           
                                                                             
                                                                   
                                                                                                          
                                                                                                     
              
                                                                                                                                  
                                                                                                           
                                                                           
                                                               
                                                                             
                                                  
                                                                   
                                                            
                                                                                                                    
                                                         
                                                                                                 
                                                         
                                                                                                     


end Taper
end Zeta23

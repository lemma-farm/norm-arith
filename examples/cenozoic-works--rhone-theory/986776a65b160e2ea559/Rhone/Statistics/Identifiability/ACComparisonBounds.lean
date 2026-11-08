/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.AbsolutelyContinuousClock
public import Mathlib
/-! # Absolutely continuous scalar comparison -/

@[expose] public section

open Set Filter MeasureTheory

namespace Rhone.Statistics.Identifiability

theorem ac_endpoint_le_of_ae_deriv_nonpos {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x, x ∈ uIcc a b → deriv f x ≤ 0) :
    f b ≤ f a := by
  have hle : (∫ x in a..b, deriv f x) ≤ ∫ _ in a..b, (0 : ℝ) := by
    apply intervalIntegral.integral_mono_ae_restrict hab hf.intervalIntegrable_deriv
      intervalIntegrable_const
    change ∀ᵐ x ∂volume.restrict (Icc a b), deriv f x ≤ 0
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hderiv] with x hx hxmem
    exact hx (by simpa only [uIcc_of_le hab] using hxmem)
  rw [hf.integral_deriv_eq_sub] at hle
  simpa only [intervalIntegral.integral_zero, sub_nonpos] using hle

theorem ac_endpoint_le_of_ae_hasDerivAt_nonpos {f fDot : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hfd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (fDot x) x)
    (hnonpos : ∀ᵐ x, x ∈ uIcc a b → fDot x ≤ 0) :
    f b ≤ f a := by
  apply ac_endpoint_le_of_ae_deriv_nonpos hab hf
  filter_upwards [hfd, hnonpos] with x hdx hnx hx
  rw [(hdx hx).deriv]
  exact hnx hx

                                                              
                                               
                                                   
                                 
                     
                                                           
                                                            
                                         
                       

                                                                        
                                               
                                                        
                                                 
                                 
                                           
                                                 
                     
              

theorem ac_comparison_upper (f fDot H HDot : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hfd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (fDot x) x)
    (hHd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt H (HDot x) x)
    (hle : ∀ᵐ x, x ∈ uIcc a b → fDot x ≤ -HDot x * f x) :
    f b ≤ f a * Real.exp (H a - H b) := by
  have hac : AbsolutelyContinuousOnInterval (fun x => f x * Real.exp (H x)) a b :=
    hf.mul (ac_exp hH)
  have hg : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt
      (fun y => f y * Real.exp (H y))
      (fDot x * Real.exp (H x) + f x * (Real.exp (H x) * HDot x)) x := by
    filter_upwards [hfd, hHd] with x hfx hHx hx
    exact (hfx hx).mul (hHx hx).exp
  have hgnonpos : ∀ᵐ x, x ∈ uIcc a b →
      fDot x * Real.exp (H x) + f x * (Real.exp (H x) * HDot x) ≤ 0 := by
    filter_upwards [hle] with x hx hxmem
    have h := mul_le_mul_of_nonneg_right (hx hxmem) (Real.exp_pos (H x)).le
    nlinarith
  have h := ac_endpoint_le_of_ae_hasDerivAt_nonpos hab hac hg hgnonpos
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (H b))).mp
  calc
    f b * Real.exp (H b) ≤ f a * Real.exp (H a) := h
    _ = (f a * Real.exp (H a - H b)) * Real.exp (H b) := by
      rw [mul_assoc, ← Real.exp_add, sub_add_cancel]

                                                             
                                                             
                                               
                                                        
                                                        
                                                         
                                          
                                   
                                                  
                                       
                       
                                                                     
                                       
                       
                                                                             
                                  
                                              

end Rhone.Statistics.Identifiability

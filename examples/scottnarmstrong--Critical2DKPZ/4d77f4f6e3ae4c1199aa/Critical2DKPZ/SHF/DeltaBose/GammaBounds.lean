/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# Gamma estimates for the scalar collision density

A unit interval in the Gamma integral gives a lower bound at every exponential
rate. Together with the recurrence, this supplies an integrable majorant for
`t^(u-1) exp(θu) / Γ(u)` without Stirling's formula. The positive minimum of
Gamma gives the sharper bound needed at small times.
-/

public section

open MeasureTheory Set

namespace Critical2DKPZ.DeltaBose

/-- Restricting the Gamma integral to `[R,R+1]` yields an exponential lower bound. -/
theorem exp_neg_mul_rpow_le_gamma_add_one {u R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    Real.exp (-(R + 1)) * R ^ u ≤ Real.Gamma (u + 1) := by
  have hi : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ u) (Ioi 0) := by
    simpa only [add_sub_cancel_right] using Real.GammaIntegral_convergent (by linarith : 0 < u + 1)
  have hsub : Icc R (R + 1) ⊆ Ioi (0 : ℝ) := fun _ hx => hR.trans_le hx.1
  have hib := hi.mono_set hsub
  calc
    Real.exp (-(R + 1)) * R ^ u
      = ∫ _x in Icc R (R + 1), Real.exp (-(R + 1)) * R ^ u := by
        simp [Real.volume_Icc, Measure.real]
    _ ≤ ∫ x in Icc R (R + 1), Real.exp (-x) * x ^ u := by
      apply setIntegral_mono_on (integrable_const _) hib measurableSet_Icc
      intro x hx
      exact mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg hx.2))
        (Real.rpow_le_rpow hR.le hx.1 hu.le) (by positivity) (by positivity)
    _ ≤ ∫ x in Ioi 0, Real.exp (-x) * x ^ u :=
      setIntegral_mono_set hi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hx.le _))
        (Filter.Eventually.of_forall hsub)
    _ = Real.Gamma (u + 1) := by
      rw [Real.Gamma_eq_integral (by linarith : 0 < u + 1)]
      simp only [add_sub_cancel_right]

/-- A reciprocal Gamma bound at any prescribed exponential rate. -/
theorem inv_gamma_le_exp_mul {u R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    (Real.Gamma u)⁻¹ ≤ Real.exp (R + 1) * u * R ^ (-u) := by
  have hg := Real.Gamma_pos_of_pos hu
  have h := exp_neg_mul_rpow_le_gamma_add_one hu hR
  rw [Real.Gamma_add_one hu.ne'] at h
  have hp := Real.rpow_pos_of_pos hR u
  have he := Real.exp_pos (R + 1)
  have heq : Real.exp (R + 1) * Real.exp (-(R + 1)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.rpow_neg hR.le, inv_le_iff_one_le_mul₀ hg]
  calc
    1 = Real.exp (R + 1) * (Real.exp (-(R + 1)) * R ^ u) * (R ^ u)⁻¹ := by
      rw [← mul_assoc, heq, one_mul, mul_inv_cancel₀ hp.ne']
    _ ≤ Real.exp (R + 1) * (u * Real.Gamma u) * (R ^ u)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h he.le) (inv_nonneg.mpr hp.le)
    _ = (Real.exp (R + 1) * u * (R ^ u)⁻¹) * Real.Gamma u := by ring

                                                                           
                                                                                      
                                                       
                                                                                       

                                                                                         
                                 
                                                                    
                                          
                                              
                                     
                                
                                        
                                          
                                                   
                                                                                           
                                                          

                                                                             
theorem integrableOn_mul_exp_neg {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-(r * u))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num) (by norm_num) hr)

                                                   
                                                   
                                                             
                                                              
                                                                                                                           

end Critical2DKPZ.DeltaBose

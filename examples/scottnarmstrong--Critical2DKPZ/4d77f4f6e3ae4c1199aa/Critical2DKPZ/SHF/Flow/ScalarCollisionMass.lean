/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ScalarLaplace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! The Laplace transform bounds short-time collision mass by choosing the damping rate at the reciprocal time scale. -/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Flow

/-- The scalar collision density is integrable on finite positive-time intervals and satisfies its Laplace bound. -/
theorem integral_scalarDensity_Ioo_le_laplace {θ rate v : ℝ}
    (hrate : 0 < rate) (hθ : θ < Real.log rate) :
    IntegrableOn (scalarDensity θ) (Ioo 0 v) ∧
      (∫ s in Ioo 0 v, scalarDensity θ s) ≤ Real.exp (rate * v) / (Real.log rate - θ) := by
  let F := fun s => Real.exp (-(rate * s)) * scalarDensity θ s
  have hF : IntegrableOn F (Ioi 0) := integrable_scalarDensity_laplace hrate hθ
  have hpoint (s : ℝ) (hs : s ∈ Ioo 0 v) :
      scalarDensity θ s ≤ Real.exp (rate * v) * F s := by
    have harg : 0 ≤ rate * (v - s) := mul_nonneg hrate.le (sub_nonneg.mpr hs.2.le)
    calc
      scalarDensity θ s ≤ Real.exp (rate * (v - s)) * scalarDensity θ s :=
        le_mul_of_one_le_left (scalarDensity_pos θ hs.1).le (Real.one_le_exp harg)
      _ = Real.exp (rate * v) * F s := by
        dsimp only [F]
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hsub : Ioo (0 : ℝ) v ⊆ Ioi 0 := Ioo_subset_Ioi_self
  have hbound := (hF.mono_set hsub).const_mul (Real.exp (rate * v))
  have hms : Measurable (scalarDensity θ) := by
    change Measurable (fun s : ℝ => scalarDensity θ s)
    exact measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)
  have hj : IntegrableOn (scalarDensity θ) (Ioo 0 v) := by
    apply hbound.mono' hms.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (scalarDensity_pos θ hs.1)]
    exact hpoint s hs
  refine ⟨hj, ?_⟩
  calc
    (∫ s in Ioo 0 v, scalarDensity θ s) ≤ ∫ s in Ioo 0 v, Real.exp (rate * v) * F s := by
      apply integral_mono_ae hj hbound
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hpoint s hs
    _ = Real.exp (rate * v) * ∫ s in Ioo 0 v, F s := integral_const_mul _ _
    _ ≤ Real.exp (rate * v) * ∫ s in Ioi 0, F s := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply setIntegral_mono_set hF _ (Eventually.of_forall hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (Real.exp_nonneg _) (scalarDensity_pos θ hs).le
    _ = _ := by
      rw [show (∫ s in Ioi 0, F s) = (Real.log rate - θ)⁻¹ from
        integral_scalarDensity_laplace hrate hθ]
      rfl

                                                                                             
                                                          
                                                           
                                                
                                                                          
                                   
                                 
                                                                  
                                    
                                                                    
                                          
                                                    
                                                                               
                                     
                                              
                                                                                             
                                                                  
                                                                   
                                  
                     
                                                                                   
                                                          
                                                                      
                                                                 
                                              
                                                           
                                     
                                                                                    
                              
                                  
                        
                                        
                                                                         
                      
      
                                                                                   
                                                                   
                                    
                                      
                                                                   
                    
                         

end Critical2DKPZ.SHF.Flow

end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientOriginClauseGauge
import CKN.Core.Step4.PressureGradientGluedTimeBounds
import CKN.Core.Step4.PressureGradientGaugeMajorantHolder
import CKN.Core.Step4.PressureGradientLargeCells

/-!
# Pressure oscillation on clipped origin windows

The pressure contribution to the slice bound is controlled by its spatial
`3/2` power mass and Hölder in time. The required mass exponent is
`13/2 - 15/(2κ)`, which yields the gradient mass exponent `5 - 6/κ`.
The separate large-radius estimate is supplied by
`pressure_gradient_origin_cylinder_large_cell_le` in `PressureGradientLargeCells`.
No estimate for the complete slice majorant is asserted here.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- Hölder in a clipped time window for the pressure part of the doubled
slice estimate, retaining its spatial power mass on that same window. -/
theorem originClause_pressure_clipped_holder
    {P : ParabolicPoint → ℝ} {x : Vec3} {t r R : ℝ} (hr : 0 < r)
    (hm : AEStronglyMeasurable P
      ((volume.restrict (vec3Ball x (2*r))).prod
        (volume.restrict (Ioc (t-r^2) t ∩ Ioc (-R^2) 0)))) :
    (∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-R^2) 0,
      (ENNReal.ofReal ((2*r) ^ (-1/2 : ℝ)) *
        eLpNorm (fun y => P (y,s)) (ENNReal.ofReal (3/2 : ℝ))
          (volume.restrict (vec3Ball x (2*r)))) ^ (6/5 : ℝ)) ≤
    ENNReal.ofReal ((2*r) ^ (-3/5 : ℝ)) *
      ((∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-R^2) 0,
        ∫⁻ y in vec3Ball x (2*r), ‖P (y,s)‖ₑ ^ (3/2 : ℝ)) ^ (4/5 : ℝ) *
        ENNReal.ofReal (r^2) ^ (1/5 : ℝ)) := by
  let W := Ioc (t-r^2) t ∩ Ioc (-R^2) 0
  let J := fun s => ∫⁻ y in vec3Ball x (2*r), ‖P (y,s)‖ₑ ^ (3/2 : ℝ)
  have hJ : AEMeasurable J (volume.restrict W) :=
    (hm.aemeasurable.enorm.pow_const (3/2 : ℝ)).lintegral_prod_left'
  have h2r : 0 < 2*r := by positivity
  have heq : ∀ᵐ s ∂volume.restrict W,
      (ENNReal.ofReal ((2*r) ^ (-1/2 : ℝ)) *
        eLpNorm (fun y => P (y,s)) (ENNReal.ofReal (3/2 : ℝ))
          (volume.restrict (vec3Ball x (2*r)))) ^ (6/5 : ℝ) =
      ENNReal.ofReal ((2*r) ^ (-3/5 : ℝ)) * J s ^ (4/5 : ℝ) := by
    filter_upwards [hm.prodMk_right] with s hs
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top hs]
    norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3/2),
      show (1 / (3/2) : ℝ) = 2/3 by norm_num]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6/5),
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos h2r _),
      ← Real.rpow_mul h2r.le, ← ENNReal.rpow_mul]
    norm_num only [show (-1/2 : ℝ)*(6/5) = -3/5 by norm_num,
      show (2/3 : ℝ)*(6/5) = 4/5 by norm_num]
    rfl
  have hv : volume W ≤ ENNReal.ofReal (r^2) := by
    calc volume W ≤ volume (Ioc (t-r^2) t) := measure_mono inter_subset_left
         _ = _ := by rw [Real.volume_Ioc]; congr 1; ring_nf
  rw [lintegral_congr_ae heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply mul_le_mul' le_rfl
  have hh := lintegral_rpow_le_rpow_lintegral_mul_measure hJ
    (by norm_num : (0 : ℝ) < 4/5) (by norm_num : (4/5 : ℝ) < 1)
  simp only [Measure.restrict_apply_univ, show (1-4/5 : ℝ) = 1/5 by norm_num] at hh
  exact hh.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hv (by norm_num)))

                                                                         
                                                          
                                            
                                                                
                
                                
                                                
                                                          
                                                       
                                                         
                                                     
                                          
                                            
                                                             
                                                              
                                                           
                                                        
                                                       
                                                                            
                
      
                                           
                                                                   
                                              
                                                   
               
                                                                       
                                                               
                                                      
                              
                                                        
                                                                          
                                                       
                                                                
                                 
                               
               
          
                                                                   
                                              
                                                              
                                                                   
                   
                                                              
                                                                                
                                   

                                                 
                                      
                                                                    
                                                        
                                                            
                                             
                                                                       
                                                                                
                                                                                        
                                                                                   
                                           

                                                                        
                                                                               
                                                                                  
                                                                                        
                                                
                                           
                                                                    
                                                        
                              
                                                                   
                                     
                                                   
                                     
                                                                         
                                                 
                                                      
                                                            
                                                                          
                                      
                                                                 
                                                              
                                     
                                                   
                                                
                                       
                                                                                    
                                        
                                                                    
                                                                
                                                  
                                                             
                         
                                            
                                                                  
                                                                                          
                                                                                     
                                                                                    
                                                                  
                                                
              
                                                           
                                   
                                                                             
                                       
                                                                                                   
                                   
                                                                                 
                                       
                               
                                          
                                                  
                                                                                   
                                                 
                                   
                                                                                      
                               
                        
                                                       
                                                                                   
                                            
                                                                           
                                                                              
                               
                                 

end CKN.Core.Step4

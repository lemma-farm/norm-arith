-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Caccioppoli.I1
import CKN.Pressure.ParamExtension
import CKN.Pressure.Slices

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

                                       
                                                  
                                         
                                      
                                               
                                          
                                                      
                       
                                                                  
                         
                                                                   
                                    
                                                       
                                                          
                                    
                                    
                                    
                                                           
                                                 
                                                               
                                                                
                             
               

                                              
                                      
                                                                    
                                                        
                                                            
                                           
                                                                    
                       
                                     
                                                                       
                                                                          

theorem caccioppoli_I2_velocity_integral_identity
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hfin : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    :
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) =
      ENNReal.ofReal (ρ ^ 2 * gamma u z ρ ^ 3) := by
  have hcube := gamma_cube_eq u z ρ hρ
  have hmul : ρ ^ 2 * gamma u z ρ ^ 3 =
      (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
    rw [hcube]
    rw [← mul_assoc]
    have hpow : ρ ^ 2 * ρ ^ (-2 : ℝ) = (1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hρ]
      norm_num
    rw [hpow, one_mul]
  rw [← ENNReal.ofReal_toReal hfin, hmul]

                             
                                                   
                               
                                                   
                  
                              
                                                      
                                                    
                                                  
                                 
                            
                                                            
         
      
                                                             
                           
             
          
                                    
                                                         
                                                         
                                                     
            
                               
                                                         
                                                                   
                                                        
                                                         

                                    
                                       
                                          
                           
                                           
                                                         
                                
                                   
                                           
                                                
            
               
                                                
                                                        
                                                                      
      
                                                                     
                                             
            
                                                        
                                                      

end CKN

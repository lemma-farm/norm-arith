-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Finiteness

open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

set_option autoImplicit false

noncomputable section

namespace CKN

                                                                 
                                                                            
                  
                           
                                      
                                                        
                                                  
            
              

                                                                
                                                                                   
                                               
                             
                                           
                                                               
                                                 
            
              

                                                               
theorem gamma_cube_eq (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ)
    (hr : 0 < r) :
    gamma u z r ^ 3 = r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
  rw [gamma, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · positivity

                                                               
                                                                           
                  
                                    
                                           
                                                        
                                                  
            
              

                                                                                
                                                         
                                                            
                        
                             
                                             
                                                                    
             
               
                                           
                                                               
                         
              
                                            
                                                                                 
                                             
                                                                    
                           
                                                     
                           
      
                      
                                             
                                                                                   
                               
                                                
                                                                  
                                 
                                                                      
                          

                                                                                     
theorem setIntegral_eq_toReal_setLIntegral_of_nonneg
    {α : Type*} [MeasureSpace α] {s : Set α} {g : α → ℝ}
    (hg : IntegrableOn g s volume) (hgn : 0 ≤ᵐ[volume.restrict s] g) :
    ∫ x in s, g x =
      (∫⁻ x in s, ENNReal.ofReal (g x)).toReal := by
  have hnon : 0 ≤ ∫ x in s, g x := integral_nonneg_of_ae hgn
  rw [← ENNReal.toReal_ofReal hnon]
  rw [ofReal_integral_eq_lintegral_ofReal hg hgn]

end CKN

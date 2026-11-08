-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Kernel

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The absolute integral on a positive cylinder is controlled by its Morrey norm. -/
theorem cylinderAbsIntegral_le_morreyNorm {q : ℝ} (hq : 1 ≤ q)
    {f : ParabolicPoint → ℝ} (_ : AEMeasurable f volume)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |f w|) ≤
      (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) * morreyNorm 1 q f := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hcell : morreyCell 1 q f z r ≤ morreyNorm 1 q f := by
    unfold morreyNorm
    exact le_iSup_of_le z (le_iSup_of_le ⟨r, hr⟩ le_rfl)
  have hcell' : (ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q))) *
      cylinderPowerIntegral 1 f z r ≤ morreyNorm 1 q f := by
    simpa [morreyCell, one_div, hq0.ne'] using hcell
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrtop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv : (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) *
      (ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q))) = 1 := by
    rw [← ENNReal.rpow_add _ _ hr0 hrtop, add_neg_cancel, ENNReal.rpow_zero]
  calc
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |f w|) =
        cylinderPowerIntegral 1 f z r := by
      unfold cylinderPowerIntegral
      apply lintegral_congr
      intro w
      simp
    _ = (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) *
          ((ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q))) *
            cylinderPowerIntegral 1 f z r) := by
      calc
        cylinderPowerIntegral 1 f z r =
            1 * cylinderPowerIntegral 1 f z r := by rw [one_mul]
        _ = ((ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) *
              (ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q)))) *
            cylinderPowerIntegral 1 f z r := by rw [hinv]
        _ = _ := by ac_rfl
    _ ≤ (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) * morreyNorm 1 q f :=
      by
        simpa [mul_comm] using
          (mul_le_mul_left hcell' ((ENNReal.ofReal r) ^
            (5 * (1 - 1 / q))))

                                                                 
                                  
                                     
                           
                                                           
                                                 
                                          
                       
             
              
                                    
                                                                       
                                
                                                     
             
           
        
                                           
                                
                                                      
                                                                      
              
                                                 
                                         
                         

                                                                  
                                                
                                                      
                                    
                         
                               
                                               
                       
             
                               
                       
                              
                                               
                                                        
                                                                    
                                           
                                          
                                                                        
                                    
        
                                                    
                                             
                                              
                                                 
                                          
                                                                        
                                    
        
                                                                 
                                                              
                                                               
                                              
                                                                     
                                              
                                                                                    
                                                               

                                                                                      
                                 

                                                                             
                                             
                                                     

                                                                                
                                                                           
               
                                                             
                        
                 
                                          
                                             
                                            
                                             
                           
                                                              
                                                         
                                                      
                                                 
                                             
                                            
                                             
                           
                                                              
                                                         
                                                      
                                                 

                                                                              
                                                                    
            
                                                 
                                

                                                                                 
                             
                                     
                     
                                           
                                                                 
                                   
                                           
                                           
                                           
                                           
        
                                            
                                                   
                                       
                                               
                                           
                                   
                                                                            
                                     
                                                 
                                                           
                                               

                                                              
                                              
                                                 
                                                               
                                 
                                                          
                                                             
                                                              
                                                    
                                    
                                          
                                                   
                       
             
              
                       
             
              
                         
                                  
                                             
              
                                           
                                            
                                                                 
                         
                                                              
                               
              
                                                                      
                                                    
                                    
                              
                                                  
                                          
                               
                          
                                                              
                       
                           
                                             
                                                                           
                                               
                                                                           
        
                                         
                                       
                                                                    
                                     
                                                        
                                  
                                                     
                                                      
      
                                 
                                                            
                                                                          
         
                                                    
                                       
                                         
                                                 
                                                                   
                                         
                                         
                                                     
                                                    
                                         
                                                         
                                           
                                         
                                                         
                                
        
                                                        
                                                                
               
                            

                                                                  
                                                  
                                                           
                                                              
                             
                                
                                                           
                                              
                                        
                                  
                              
                        
                                                   
                       
             
                                  
                         
                                                               
                        
             
                                                    
                          
             
                               
                        
             
                                         
                          
             
                               
                                
                                                                      
                                  
                                                       
                                        
                                                                      
                                          
                                                       
                                                    
                           
                
                                           
                                                                    
                                                   
                                       
        
                                         
                                                      
                                                                 
                
                                                 
                                                                         
                                           
               
            
                                                                
                                 
                                                   
                
                                                                      
                                                       
                   
                                                                     
                              
                                             
      
                                               
                                             
                                   
                                      
                                               
                                                      
                                  
                                           
                                         
               
                        
                      

                                                                     
                                                                               
                                         
                                                          
                                            
                                                               
                                                                
                                          
           
                                                  
                                                          
                                               
               
                       
                                                             
                          
                                                              
                                
                                                            
                                           
      
                                         
                                                            
                         
                                                              
                               
                              
                                                                     
                                              
                                                                 
         

                                                            
                                                   
                                      
                                                   

                                                                         
                                                       
                                                                                
                                         
                                                          
                                       
                                                                 
                                                  
                                  
                                                                   
                       
                                   
                                                            
                                  
                                                                         
           
                                                                 
        
                                   
                                                              
                                                                 
                                                                  
                                                        
                                    
                                                                         
                                                      
      
                                         
                                                            
                                              
                                                                   
                                            
                                                                    
                                
                                                     
                               
                                    
                                                                      
                       
                                       
                                                                             
                
           
                                                               
         
                                         
                                                                   
         



end CKN.Foundation.Parabolic.Morrey

module

public import AmbidextrousSofa.Analysis.ProperExcessScalar
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Exact late-excess estimates for the tilted first wing

Compare the tilted floor energy with the zero-tilt trajectory. Tilt
delays the first zero by at most its height, but shortens the subsequent
excess by at least that height. The two effects cancel, and the entire
range inherits the zero-tilt stopping bound.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Analysis

/-- The strict endpoint-angle margin follows from a quadratic cosine
bound at the half-angle and the exact double-angle identity. -/
theorem cos_eleven_fifteenths_gt_thirty_seven_fiftieths :
    37 / 50 < Real.cos (11 / 15 : ℝ) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := (11 / 30 : ℝ))
  rw [show (11 / 15 : ℝ) = 2 * (11 / 30) by norm_num, Real.cos_two_mul]
  nlinarith

theorem eleven_fifteenths_lt_arccos_of_le {C : ℝ}
    (hC0 : -1 ≤ C) (hC1 : C ≤ 37 / 50) :
    11 / 15 < Real.arccos C := by
  rw [← Real.arccos_cos (x := 11 / 15) (by norm_num) (by linarith [Real.pi_gt_three])]
  exact Real.arccos_lt_arccos hC0
    (by linarith [cos_eleven_fifteenths_gt_thirty_seven_fiftieths]) (Real.cos_le_one _)

                                                                    
                                               
                                                
                                      
                                          
                                        
                                        
                                          
                                                              
                                                                         
                                            
               
                                 
                                                                       
                                                                                          
              
                                                                                      
                                  
                                                                            
                                  
                                                                      
                                                                                   


                                                                       
                                                                       
                                                            
                                                
                                 
                                                                                
                 
                                               
                             
                                                                        
                                                      
                                                                     
                                                             

                                                
                                                
                                                        
                                                         
                                                                              
                                                                  
                                                 
                                                        
                                 
                                                 
                                       

                                                    
                                                              
                                                         
                                               
                                                                     
                                                    
                                        
                                  
                                               
               
                                                                          
                                            
                                                           
                                                                                      
                                                                     
                          

                                                                                         
                                                 
                                                                      
                                                      
                              
                                                    
                                             
                                                    
                                                 
                                                        
                                                               
                                                                     
                                                                        
                                               
                     
                                                                   
                                                                     
                           
                                                                       
            
                                                                   
                                                                                            
                                                      
                                           
                                                                
                                                                                        
                                                        
                                                                                       
                              
                                                                  
                                                                                      
                                                                 
                                
                              
                                    
                                             
                                                                           
                                             
                                                                                 
                            
                                                                                         
                                                                             
                                                                                        
                                 
          

end AmbidextrousSofa.Analysis

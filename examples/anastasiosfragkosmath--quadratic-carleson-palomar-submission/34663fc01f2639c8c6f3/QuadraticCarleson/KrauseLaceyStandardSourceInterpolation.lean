import QuadraticCarleson.KrauseLaceyStandardSourceLinf

/-!
# Source-faithful interpolation for the scalar-standard contribution

At one physical scale the source proof combines a local-average `L∞` bound
with the already established squared `L²` estimate.  The interpolation here
is applied to that fixed output function itself.  This is important because
the stopping collection depends on the input, so it would be incorrect to
silently treat the construction as a fixed operator and invoke an operator
interpolation theorem.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- Direct interpolation of one output function between a pointwise bound
and its squared `L²` mass. -/
theorem lintegral_enorm_rpow_le_linf_mul_sq
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (F : ℝ → E) {M q : ℝ} (hM : 0 ≤ M) (hq : 2 ≤ q)
    (hbound : ∀ x, ‖F x‖ ≤ M) :
    (∫⁻ x, ‖F x‖ₑ ^ q) ≤
      ENNReal.ofReal (M ^ (q - 2)) * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℕ) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  change ‖F x‖ₑ ^ q ≤ ENNReal.ofReal (M ^ (q - 2)) * ‖F x‖ₑ ^ (2 : ℕ)
  calc
    ‖F x‖ₑ ^ q = ‖F x‖ₑ ^ (q - 2) * ‖F x‖ₑ ^ (2 : ℕ) := by
      nth_rewrite 1 [show q = (q - 2) + 2 by ring]
      rw [ENNReal.rpow_add_of_nonneg (q - 2) 2 (by linarith) (by norm_num)]
      rw [ENNReal.rpow_two]
    _ ≤ ENNReal.ofReal (M ^ (q - 2)) * ‖F x‖ₑ ^ (2 : ℕ) := by
      gcongr
      rw [← ENNReal.ofReal_rpow_of_nonneg hM (by linarith)]
      apply ENNReal.rpow_le_rpow
      · rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbound x)
      · linarith

                                                                     
                 
                                                         
                                                                         
                                                    
                                 
          

                                                                        
                                      
                                                               
                                                             
                                                             
                                                          
                                                                                   
                                            
                                                
                                                                   
                                                    
                                                   
                                            
                                    
                                                                            
                                           
                                        
                      
                                                                            
                                   
                                                            
                                
                                                   
                                               

                                                                       
                                                           
                                                                 
                                                             
                                                             
                                                          
                                                                                   
                                            
                                                
                                                                   
                                                  
                          
                                                   
                                      
                    
                                                                                    
                                      
                                                                              
                                             
                                            
                                                                 
                                                                              
                                         
                                                                 
                                                      
                                 
                                                            
                                                               

                                                           
                                                          
                                                             
                                                             
                                                          
                                                                                   
                                            
                                                
                                                                   
                                                  
                          
                                                    
                                                        
                     
                                                                                    
                                      
                                                                              
                                                        
                                                     
                                        
                                             
                        
                                                                        
                                 
                            
                                                              
                                                  
                               

                                                                            
                                                          
                                                                     
                                                             
                                                                 
                              
                                                          
                                                                                   
                                            
                                 
                                        
                                                      
                                                       
                        
                                                                   
                                                    
                               
                                                                            
                                           
                                        
                                                                                    
                                      
                                   
                                                            
                                
                                                         
                                                      

                                                                            
                                                                        
                                                                       
                                                             
                                                                 
                              
                                                          
                                                                                   
                                            
                                 
                                        
                                                      
                                                       
                                             
                                                                   
                                              
                    
                                                                                    
                                 
                                                                              
                                             
                                            
                                                            
                                  
                                                                              
                                         
                                                                                  
                                                             
                                 
                                                                  
                                                                      

                                                        
                                                                
                                                             
                                                                 
                              
                                                          
                                                                                   
                                            
                                 
                                        
                                                      
                                                       
                                             
                                                                    
                                                                
                     
                                                                                    
                                 
                                                                              
                                                        
                                                     
                                        
                                             
                        
                                                                        
                                 
                            
                                                                    
                                                         
                               


end KrauseLaceyBadScale
end QuadraticCarleson

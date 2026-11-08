module

public import RequestProject.FlowC2

/-!
# `C¹` stability of flows under perturbation of the field

If two fields `V`, `W` satisfy the standing hypotheses and are uniformly `δ₀`-close with
derivatives `δ₁`-close, then their flow maps over a time `T` are `C¹`-close, with an error
`O(δ₀ + δ₁)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {V W : ℝ → E → E} {M K : ℝ≥0} {K2 K3 : ℝ} {t₀ t₁ : ℝ}

                               
                                                                                      
                                                                
                                                                                         
                                                     
                                                                                      
                                                                                             
                                  
                                                                              
                  
                                                            
                                                         
                                                                    
            
                                                             
                                                                      
                                               
                                            
                                                      

                                               
                                                                                   
                                                              
                                       
                                                                                       
                                                               
                                                                                            
                                                  
                                                       
                                                       
                           
                                
                                                
                                                
                                            
                                                                               
                          
                                          
                                                                                 
                                   
                                                                  
                                                                   
                                                                                 
                                                                                            
                                               
                                                
                                               
                                                
                                                                                         
                                                                       
                                             
            
                                                  
                                              
                                                                           
                                                                                   
                                                                  
                                                           
                                                  
              
                                                                   
                                                
                                        
                                 
                                          
                                                                    
                                                                     
                                                                     
                                          
                                   
                                       
                                       
                                                                                                 
                                                                         
                                                                                      
                                          
                  
                                                                
                                                                    
                                                         
                                                      
                            
                 

                                           
                                           
                                                                                                 
                                
                                

                                                        
                                                                               
                                                              
                                       
                                                                                  
                                                             
                                                                                         
                                                
                                 
                                       
                                                                
                                                                                      
                                         
                                                                                      
                                         
                                            
                                              
                                               
                     
                                                                                      
                                                                                         
                                           
                                           
                
                     
                                                   
                   

end AnomDiss

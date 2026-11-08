/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiSq

/-!
# Products of single and pair integrals with general exponents

With `r = s(y - x)`, `r' = s(y' - x)`, `d = s(y - y')`:

* `i2Psi2LintBound_diag_prod_single`:
  `(∫ |A| s(y' - w)^(-e₁)) (∫ |A'| s(y - w')^(-e₂)) ≲ B² r^γ₁ r'^γ₂ (d^(-p₁) + r'^(-p₁))
  (d^(-p₂) + r^(-p₂))`, `pᵢ = γᵢ + eᵢ - 2 ∈ [0, 1]`;
* `i2Psi2LintBound_diag_prod_pair`: the same for
  `(∫ |A| s(y - w)^(-e₁) s(y' - w)^(-e₂)) (∫ |A'| s(y' - w')^(-e₃) s(y - w')^(-e₄))`,
  with `p₁ = γ₁ + e₁ + e₂ - 2`, `p₂ = γ₂ + e₃ + e₄ - 2`.
-/

public section

open MeasureTheory

namespace RegularityStructures

                                                              
                                                                                          
                                                                                        
                                                                          
                                                                         
                                                                                              
                                         
                                                                
                                                                                 
                                                                                  
                                                                                           
                                                             
                                                               
                                                             
                                                                   
                                                                               
                                                                               
                                         
                               
                                    
                                           
                                                                                   
                                                                                      
                                                                                    
                                                                                 
                                                    
                                 
                                 
                                                           
                                                       
                                                          
                                                                                       
                                                                    
                                                   
                                                                  
                                                    
                                                                 
                                                           
                                        
                                                                                     
                         
                                                                                     
                        
                                                                                    
                        
                                                          
                                                          
                                                          
                                                         
                             
                             
                             
                             
                                                      
                                                             
                                                                   
                                                                                     
                                                       
                                                       
                                                        
                                                                    
                                                                                     
                                                            
                                                       
                                                         
                                                                                       
                                                                              
                                                                        
                                                                         
                                                                        
                                
                    

                                                            
                                                                                              
                                                                                         
                                                                          
                                                                    
                                                               
                                                                         
                                                                                              
                                         
                                                                
                                                                                
                                                       
                                                                                    
                                                     
                                                                                           
                                                                  
                                                                    
                                                                  
                                                                        
                                                                                        
                                                                                        
                                          
                               
                                    
                                           
                                                                                   
                                                                                      
                                                                                    
                                                                                 
                                                    
                                      
                                        
                                                           
                                                            
                                                             
                                                                   
                                                        
                                                                                     
                                                                    
                                                   
                                                       
                                                                     
                                                    
                                                        
                                                                    
                                                                                 
                                        
                                                                                          
                         
                                                                                         
                        
                                                                                          
                        
                                                               
                                                               
                                                               
                                                              
                             
                             
                             
                             
                                                      
                                                                           
                                                                   
                                                                                     
                                                       
                                                            
                                                            
                                                                  
                                                                    
                                                                                     
                                                            
                                                            
                                                            
                                                                   
                                                        
                                                                                     
                                                                              
                                                                        
                                                                         
                                                                        
                                
                    

end RegularityStructures

end

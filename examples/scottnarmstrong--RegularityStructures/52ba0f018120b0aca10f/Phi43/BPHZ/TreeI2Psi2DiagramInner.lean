/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramKernel

/-!
# Integrals of the kernel increment against singular weights

With `A(w) = K(y - w) - K(x - w)` and `r = s(y - x)`:

* `i2Psi2LintBound_kernel_sub_two`: `∫ |A(w)| s(g - w)^(-2) dw ≲ B r^θ (s(y - g)^(-θ) + s(x - g)^(-θ))`
  for `θ ∈ (0, 1]`;
* `i2Psi2LintBound_kernel_sub_three`: `∫ |A(w)| s(g₁ - w)^(-1) s(g₂ - w)^(-κ) dw ≲
  B r^θ (s(y - g₂)^(-(θ+κ-1)) + s(x - g₂)^(-(θ+κ-1)) + 2 s(g₁ - g₂)^(-(θ+κ-1)))` for
  `θ ∈ [0, 1)` and `θ + κ > 1`;
* `i2Psi2LintBound_kernel_sub_slab`: `∫ |A(w)| s(g₁ - w)^(-λ₁) s(g₂ - w)^(-λ₂) dw ≲ B r^θ` when
  `3 + θ + λ₁ + λ₂ < 5` (no singular output), under the support hypotheses.

The constants depend only on the exponents.  [Hai14, Lemma 10.14, Lemma 10.18].
-/

public section

open MeasureTheory

namespace RegularityStructures

                                                                   
                                                                                                      
                                                                                               

                                                                               
                                                                          
                                                               
                                                      

                                                                                    
                                                                           
                                                           
                                                  
                                                        
                                                    
                                                         
                                                                                             
                                                                                            
                                                                  
                                                  
                                                   
                                                                                          
                                                                                   
                                                                         
                                     
                                    
                                                
                       
                       
                 
                                                                           
                                                                                           
                                                           
                                                                       
                                                                          
                                                                      
                                                                                   
                                          
                                                                                   
                
                                                                                   
                                                          
                                                    
                                                                        
                                                                                             
                                                                                              
                                       
                    

                                                                                               
                                                                                           
                                     
                                                           
                                                  
                                                        
                                                    
                                                         
                                                                                             
                                                                
                                                                            
                                                                  
                                                                                          
                                                   
                                                           
                                                            
                                                                       
                                                                                   
                                                    
                                     
                                         
                                                          
                       
                       
                        
                    
                                                 
                                                                                 
                                         
                                                                  
                                                                           
                                                                                              
                                                                       
                                                                       
                                                                       
                                                                                                  
          
                                                                      
                                                                                   
                                          
                                                                                   
                                                                                              
                                                                                      
                                                                                                
                                 
                                                                                                 
           
                                                                                                 
           
                                          
                  
                                                                                                      
                                              
                                              
                                                                            
                                             
                                                                                             
                                                                                               
                                                                                
                                                 
                                                                                             
                                                
                                                                                              
                                                          
                                                 
                                                                                               
                                                
                                                                                                
                                                     
                                                                       
                                                             
                                
                    

                                                                       
                                                                                                
                                               
                                                           
                                              
                                                  
                                                        
                                                    
                                                         
                                                                                             
                                                                                      
                                                                  
                                                                                      
                                                        
                                                                                         
                                                     
                                     
                                                
                                           
                                       
                                       
                                       
                                                                              
                                                                                      
                                                        
                                                                                    
                                                        
                                                    
                                                      
                                                                                      
                                                          
                                                                                
                                                                                          
                                                         
                                                    
                                                                                      
                                                                                       
                                                                      
                                                                                   
                                          
                                                                                   
                  
                                                                     
                                                                                            
                                 
                                                                       
                                              
                                                                      
                                                                                               
                                                                                        
                                       
                    

end RegularityStructures

end

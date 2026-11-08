/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramFour

/-!
# The cross pairings of the tree `I(Ψ²) Ψ²`

Three covariance weights couple the two integration variables `w, w'` of the diagram integral
`∫∫ A(w) A'(w') χ(w, w')`: one in `w` only (`c₁`, singular at a point `g₁`), one in both
(`c₂`, singular on the diagonal `w = w'`), one in `w'` only (`c₃`, singular at a point `h`).
With `|cᵢ| ≤ 2 B s^(-1)` and `a ∈ (0, 1/2)`,
`∫∫ |A| |A'| |c₁| |c₂| |c₃| ≲ B⁵ s(y - x)^a s(y' - x)^a` (`i2Psi2LintBound_chaos4_cross`).
The inner integral is `i2Psi2LintBound_kernel_sub_three` (total order `5 + a`), the outer
integral is bounded (`i2Psi2LintBound_kernel_sub_slab`, total order `3 + a + a + 1 < 5`).
This covers the pairing `c₀₂ c₀₃ c₁₂` of chaos `4` and `c₀₁ c₂₃ c₀₂` of chaos `2`
[Hai14, p. 169-170].
-/

public section

open MeasureTheory

namespace RegularityStructures

                                                                                        
                                                                             
                                                                          
                                                              
                                              
                                                  
                                                        
                                                    
                                                         
                                                                                             
                                                                                                
                                                                                        
                         
                                               
                                                                      
                                                  
                                                                         
                                                
                                                                       
                                                                
                                                                      
                                                 
                                                                                              
                                                                                  
                                                     
                                                                                            
                                                 
                                          
                                                                                           
                                           
                                    
                                             
                                                
                                                                          
                                                                            
                                                                                    
                                                    
                                               
                                     
                                                                                                      
                                                                          
                                                                                                 
                                                                              
                                                                           
                                                                      
                                                 
                                                                   
                                                                                     
                                                                                             
                                                
                  
                                                                                                      
                      
                                                                                     
                       
                                                                
                                                                            
                                             
                                                                                                      
                        
                           
                         
                                                                     
                                            
                                                                     
                                            
                                                  
                                                                    
                                                                             
                                              
                                                                  
                                        
                                                                   
                                                             
                                                                
                                                                  
                                            
                                                   
                                                                                  
                                                                           
                                                                                     
                                           
                                                                     
                                                                                          
                                                                                
                                                                                             
                                                                                          
                                                             
                                                         
                                                       
                                                                        
                                             
                                         
                                                           
                                                                   
                                                                                         
                              
                                                       
                                                       
                                                     
           
                

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramBound
public import Phi43.BPHZ.TreeI2Psi2DiagramInner

/-!
# The tree `I(Ψ²) Ψ²`: building blocks with general exponents

Generalisations of `i2Psi2LintBound_kernel_sub_two` and `i2Psi2LintBound_kernel_sub_three` to
arbitrary exponents of the singular weights, for the difference bound (10.3).  With
`A(w) = K(y - w) - K(x - w)`, `r = s(y - x)`, the Hölder gain `γ ∈ [0, 1]` and exponents `e`,
`e₁`, `e₂`:

* `i2Psi2LintBound_kernel_sub_single`:
  `∫ |A| s(g - w)^(-e) ≲ B r^γ (s(y - g)^(-(γ+e-2)) + s(x - g)^(-(γ+e-2)))`;
* `i2Psi2LintBound_kernel_sub_pair`:
  `∫ |A| s(g₁ - w)^(-e₁) s(g₂ - w)^(-e₂) ≲ B r^γ (s(y - g₂)^(-η) + s(x - g₂)^(-η) +
  2 s(g₁ - g₂)^(-η))`, `η = γ + e₁ + e₂ - 2`.

The kernel hypotheses are bundled in `i2Psi2KernelHyp`.  [Hai14, Lemma 10.14, Lemma 10.18].
-/

@[expose] public section

namespace RegularityStructures

                                                                                                
                                                                                             
                                                         
                                                                 
                                                                                                 
                                                                                                    
                                                                                       

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

                                                                    
                                                                                                      
                                                                                               

                                                                                
                                                                          
                                                               
                                                      

                                                                                                 
                                                                                             
                       
                                                                         
                                                                                            
                                                                  
                                            
                                                   
                                                          
                                                                 
                                                                                   
                                                               
                                     
                            
                                   
                                                           
                       
                       
                  
                                                                           
                                                                                      
                                                             
                                                                       
                                                                          
                                                                      
                                                                                   
                                          
                                                                                   
                
                                                                                 
                                                    
                                                    
                                                                  
                                                                                             
                                                                                        
                                       
                    

                                                                                         
                                                                                 
                                                                       
                              
                                                                         
                                                                
                                                                            
                                                                  
                                                                                      
                                                   
                                                                 
                                                                  
                                                                             
                                                                                         
                                           
                                     
                                 
                                   
                                                                       
                       
                       
                        
                     
                                                 
                                                                                      
                                          
                                                                       
                                                                             
                                                                                                 
                                                                        
                                                                       
                                                                       
                                                                                                  
          
                                                                      
                                                                                   
                                          
                                                                                   
                                                                                              
                                                                                   
                                                                                            
                                  
                                                                                        
           
                                                                                        
           
                                            
                                                      
                                                    
                                              
                                              
                                                                       
                                              
                                                                                             
                                                                                          
                                                                                 
                                                 
                                                                                        
                                                 
                                                                                         
                                                           
                                                 
                                                        
                                                                                                  
                                                         
                                                                                                       
                                                                       
                                                             
                                
                    

end RegularityStructures

end

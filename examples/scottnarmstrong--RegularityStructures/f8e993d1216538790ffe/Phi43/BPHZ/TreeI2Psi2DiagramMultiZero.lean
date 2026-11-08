/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiChaosTwo

/-!
# Chaos `0` of the difference bound for `I(Ψ²) Ψ²`

The mean of the field is `m(y) = -2 ∫ K(x - w) Q(w - y)² dw`.  For two scales the difference
`m_ε(y) - m_ε'(y)` involves `Q_ε² - Q_ε'²`, which gains a factor `(max ε ε')^θ` at the price of the
exponent `2 + θ` instead of `2`; the total order `5 + θ` is then above the critical `5`, with no
logarithmic loss.  The deterministic input is
`∫ |K(x - w)| s(y - w)^(-(2+θ)) dw ≲ B s(y - x)^(-θ)`
(`i2Psi2LintBound_diff_chaos0`), and its consequence for integrands dominated by it
(`integrable_and_abs_integral_diff_chaos0_le`).
-/

public section

open MeasureTheory

namespace RegularityStructures

                                                         
                                                                    
                                                                        
                                                                         
                                                         
                                                                                               
                                                           
                                                                                   
                                                                         
                                    
                     
                                    
                                                                                   
                      
                                                
             
                                   
                                                                                      
                        
                                                              
                       
                                                            
                                                      
                                                              
                                                                                                    
                                          
                      
                                                     
                                                               
                                                                        
                      

                                                                                        
                                                                                       
                                                                         
                                                                            
                                                           
                                            
                                                                          
                                                                                           
                                                         
                    
                                   
                                  
                                       
                                                                  
                                                                                                    
                                                                        

end RegularityStructures

end

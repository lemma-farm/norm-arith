/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramBounded
public import Phi43.BPHZ.KernelCalculusIncrement

/-!
# The increment of the kernel `K` against singular weights

For `K` with `|K| ≤ B s^(-3)`, increments `|K(u + h) - K u| ≤ B s(h) s(u)^(-4)` for `s(h) ≤ s(u)/2`
and time support `|t| ≤ 1`, put `A(w) = K(y - w) - K(x - w)`.  By [Hai14, Lemma 10.18] (in the form
`abs_sub_le_of_increment`), for `θ ∈ [0, 1]`,
`|A(w)| ≤ 12 B s(y - x)^θ (s(y - w)^(-3-θ) + s(x - w)^(-3-θ))`
(`abs_kernel_sub_le`), and `A` vanishes outside the slab `|t - x₀| ≤ 2` when `|y₀ - x₀| ≤ 1`
(`abs_kernel_sub_le_slab`).  Integrating against one or two further singular weights gives
the three estimates used for the diagram integrals of `I(Ψ²) Ψ²`:

* `i2Psi2LintBound_kernel_sub_two`: against `s(g - w)^(-2)` (total order `5 + θ > 5`);
* `i2Psi2LintBound_kernel_sub_three`: against `s(g₁ - w)^(-1) s(g₂ - w)^(-κ)`;
* `i2Psi2LintBound_kernel_sub_slab`: against two weights of total exponent `< 2 - θ`,
  on the slab (a bounded integral).
-/

public section

open MeasureTheory

namespace RegularityStructures

                                                                 
                                                                  
                                                                                                
                                                      
                                                    
                                                        
                                                       
                                                                                         
                                                                                                     
                                                                       
                                                                                               
                                                           
                                                       
                                                                                                  
                   
                                                     
          
                       
                                                                               
                                              
                                                
                  
         

                                                                         
                                                          
                                                                                            
                                                                 
                                             
                              
                   
                        
                               
                   
                
                 
                                             
                                   
                                                                      
                                                  
                          
                               
                   
                
                 
                                             
                                   
                                                      
                          
                       

                                                          
                                                                                       
                                                              
                                                      
                                                    
                                                        
                                                       
                                                                                         
                                                                                     
                                           
                                                                                           
                                                                                                
                                    
                                                      
        
                                                      
                                     
                                                    

end RegularityStructures

end

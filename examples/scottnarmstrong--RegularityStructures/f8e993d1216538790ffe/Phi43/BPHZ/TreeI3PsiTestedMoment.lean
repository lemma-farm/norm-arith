/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiFieldIdentity

/-!
# Pair integrability of the field `I₃Ψ`

For fixed `ε > 0` and base point `x`, and all points `y, ȳ`, the product
`I₃Ψ(y) I₃Ψ(ȳ)` is integrable on `Ω` and `E|I₃Ψ(y) I₃Ψ(ȳ)| ≤ M` with
`M = 42 C₁⁴ (2 ‖K‖_{L¹})²` (`C₁ = hairerWickConstant`), a bound uniform in `y, ȳ` (but not in `ε`).
This is the hypothesis of the tested second-moment Fubini theorem
`integral_abs_integral_mul_sq_le`; in particular `I₃Ψ(y) ∈ L²`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

                                                                           
                                                                          
                                                                      
                                            
                                                               
                                                       
                                                       
                                                                       
                                                                               
                                                                  
                                                                                       
                                                                                    
                          
                                              
                                                                                  
                                                                                
            

                                                                         
                                                                                        
                                                                                      
                                                                                              
                                                                                  
                                                                                 
                                                   
                                 
                                                 
                                                                        
                                             
                                                                                     
                                                
                                                                
                                                           
                                                   
                                                    
                                                         
                                                                                     
                                                                      
                                                                              
           
                         
                          
                                                                             
                                                                            
                                                                    
                                                                                  
                                                                                    
                                              
           
                                                                                 
                                                           
                                                            
                                                  
                                                                                        
                                                              
                                                                  
                               
                                                                                               
                                                                                                 
                                                          
                                                           
                                                                  
                                       
        
                                                                            
                         
                                                                              
                                                                            
                              
                                                                        
                                                                                 
                                                            
                                                                                                  
                         
                  
                                                                                
                                                             
                                                             
                                                   
                                      
                                                                                          
                                                   
                                                             
                                                                  
                                                                              
                                                                                          
                                     
                                                                              
                                               
                                                                
                     
                
                                                                                           
                                                                                    
                               
               
                                                                      
                                                                                   
                                                   
                                                          
                                                                       
                                                     
                                                                     
                                               
                                                                       
                                                                                                 
                       
                         

                                     
                                                                        
                                                                                   
                                                             
                                                                   
                                                                                      
                                                                             
                                             
                                                                       
                                                                           
                                                  
                                                             
                                                               
                        
                                                                   

end RegularityStructures.Phi43

end

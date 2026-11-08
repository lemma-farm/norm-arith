/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2FieldChaos

/-!
# The tree `I(Ψ²) Ψ²`: the four-argument covariance identity

With the chaos kernels `χ₄, χ₂, χ₀` of `TreeI2Psi2FieldChaos`, for `g₁, g₃ ∈ L¹`,
`E[(∫ g₁ Y₀) Y₁(y) ((∫ g₃ Y₂) Y₃(y'))] = ∫∫ g₁ g₃ χ₄ + ∫∫ g₁ g₃ χ₂ + ∫∫ g₁ g₃ χ₀`
(`hairerI2Psi2_integral_mul_four`), each piece integrable.  Integrability of the pieces follows
from the uniform bound `|Q_{ε ε'}| ≤ ∑ᵢ c_{εᵢ}` on cross covariances.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : Fin 4 → ℝ} {ξ : Fin 4 → Ω → SpaceTime → ℝ}

                                                                                             
                                                                                         
                                                                                          
                     
                                                                                               
                                                                              
                                                              
                                        
                                                                                       
                                                                                        
                         
                                                                                       
                                                                                        
                         
          

                                                                      
                                                                                     
                                                                            
                                                                                            
                                                                  
                                                                    
                                                                  
                                                                    
                                                                  
                                                                        
                                                                         
                                                        
                                                        
                                                          
                                                      
                                                        
                                                         
                                                        
                                                        
                                                        
                                                        
                                                        
                                                                        
                                                        
                                                        
                                                        
                                                        
                                                         
                                                        
                                                                               
                                                                  
                                                                   
                                                                    
                                                                   
                                                                  
                                                                 
                              
                     
                                                                                     
                                               
                                                          
                                                             
                           
                     
                                                                                     
                                               
                                                          
                                                             
                           
                       
                                                                                    
                                               
                                                          
                                                             
                           
                       

                                                                         
                                                                                            
                                                                                                 
                                                                                                
                             
                                                                                       
                                                                            
                                                                                            
                                                                                
                                                 
                                                                
                                                        
                                                                
                                                 
                                                                
                                                        
                                                     
                                                                      
                                                     
                                                                      
                                                    
                                                                         
                                       
                                                      
                                                     
                                                            
                                                                            
                                                                                               
                                                                                
                                                                             
                                                                                               
                                                                                 
                                                                             
                                                                                           
                                                           
                                                                                          
                                                                                
                                                                                     
                                                                                
                 
                                                                           
                                                                                     
                                                                               
                                                       
                                                                    
                                                                            
                                          
             
         
      

end RegularityStructures.Phi43

end

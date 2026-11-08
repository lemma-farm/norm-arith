/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiField
public import Phi43.BPHZ.TreeI3PsiFieldFubini
public import Phi43.BPHZ.TreeI3PsiFieldMoment

/-!
# The covariance identity for `I₃Ψ`

For integrable kernels `g, ḡ`, scales `ε, ε'` and points `y, ȳ` the covariance of the fields
`(∫ g :Ψ_ε³:) Ψ_ε(y)` and `(∫ ḡ :Ψ_ε'³:) Ψ_ε'(ȳ)` is
`∫∫ g(w) ḡ(w̄) [18 Q_ε(w - y) Q_{εε'}(w - w̄)² Q_ε'(w̄ - ȳ) + 6 Q_{εε'}(w - w̄)³ Q_{εε'}(y - ȳ)
  + 18 Q_{εε'}(w - w̄)² Q_{εε'}(w - ȳ) Q_{εε'}(y - w̄)] dw dw̄`,
with `Q_{εε'} = hairerCrossCovariance` (orientation `Q_{εε'}(z - z') = E[Ψ_ε(z) Ψ_ε'(z')]`).  The
proof applies Fubini on `Ω × (SpaceTime × SpaceTime)` (`integral_testedPair_eq`), justified by the
moment bound `E|:X_a³: X_b :X_c³: X_d| ≤ 42 D⁴` on the four-point Gaussian vector
`(Ψ_ε(w), Ψ_ε(y), Ψ_ε'(w̄), Ψ_ε'(ȳ))`, and the block formula
`integral_wick_three_mul_X_mul_wick_three_mul_X`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

                                                                                               
                                                                                 
                                                                                                        
                                                                       
                                                                                             
                                                                                             
                                                       

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

                                                                            
                                                                                                     
                                                                              
                                                                    
                             
                                                                                       
                                                                                   
                                                   
                                                                               
                                                                 
                                                       

                                                                                                    
                                                                                     
                                                                             
                                                                              
                                                                    
                                                                                      
                                                                             
                                                                       
                                                                              
                                                                             
                                                                      
                                                                             
                                                                                
                                                                                                   
                                                        
                                                                                       
                                                                                  
                                               
                                                                      
           
                                                                                              
                                                                     
                                                                        
                                                                             
                                                                          
                                                                            
                                                                    
                                                                                                  
                                                                      
                                                                              
                                                                    
                                                                                                  
                                                                          
           
                                                               
                                                                                       
                               
                                                             
                                              
        
               
                             
            
                                                     

                                                                     
                                                    
                                                                                               
                                                                                       
                                                                              
                                                                                     
                                              
                                                                                     
                                                                                            
                                                                        
                                                                                                   
                                                                                         
                                 
                                                
                                                                  
                                                           
                                                             
                                                   
                                                     
                                                         
                                                           
                                                               
                                                                          
                                                          
                                                                          
                                                                                
                                                                
                                                                                                   
                                                                                         
                                  
                              
           
                            

end RegularityStructures.Phi43

end

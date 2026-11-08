/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeWickSquare
public import Phi43.BPHZ.PsiGaussianVectorContinuous

/-!
# The field `I₃Ψ`: definition, measurability and integrability

With the Wick cube `:Ψ³: = Ψ³ - 3 C₁ Ψ` (`C₁ = hairerWickConstant`) we set, for a base point `x`,
`I₃Ψ(y) = (∫ (K(y - w) - K(x - w)) :Ψ³:(w) dw) Ψ(y)`
(the pathwise field behind the tree `I(Ψ³) Ψ` of [Hai14, §10]).

Because `ξ ω` is smooth, `Ψ(ω, ·)` is continuous, and the kernel `K` is integrable and vanishes
for time displacement larger than `1`; hence the inner integral converges for every `ω`.  The
field `(ω, y) ↦ I₃Ψ` is jointly measurable.

The Wick cube here is named `hairerPsiWickCubeField` (a parallel development may use
`hairerPsiWickCube`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

                                                                                    
                                                                                
                                                          
                                                                                    

                                                                                          
                                                                          
                                                                          
                                                                     
                                                                  

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

                                                                       
                                                                               
                                             
                                                                 
                                                                      
                                                                                  
                                                 
                                                                                
                                                                    
                                                                                     
                                                     
                                 
                                                        
          
                                                        
                                                                                  
                                   
                                         
                                                     
                                             
                           

                                                  
                                                                                               
                                                                                      
                                                  
                               
                                           

                                                                          
                                                                                         
                     
                                                      
                                                                           
                                                       
                                                               
                                                           
                                                              
                                           
                                                                     
                                                                                                
                                                 
                                                              
                                                  
                                                                                          
                                                                   
                                                
                          

                                        
                                                                                       
                     
                                                                                  
                                                           
                                                     
                                                                     
                                                
                                                           
                                                       

                                  
                                                                                                
                                                                
                         
                                            
                                                                                     
                                      
          
                                                                             

                                                       
                                                                                               
                                                                         
                                      

end RegularityStructures.Phi43

end

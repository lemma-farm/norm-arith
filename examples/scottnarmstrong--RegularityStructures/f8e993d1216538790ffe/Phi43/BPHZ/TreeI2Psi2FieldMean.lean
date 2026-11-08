/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2Field
public import Phi43.BPHZ.TreeWickSquareFour
public import Phi43.BPHZ.TreeWickDifferenceTested
public import RegularityStructures.Probability.RandomFieldFubini

/-!
# The tree `I(Ψ²) Ψ²`: the mean

[Hai14, (10.39)-(10.42)].  For a kernel `g ∈ L¹` and `Y = :Ψ²:`,
`E[(∫ g Y) Y(y)] = ∫ g(w) 2 Q_ε(w - y)² dw` (stochastic Fubini, the chaos-`0` part).  For the
increment kernel `g = K(y - ·) - K(x - ·)` this gives the mean of the field `(10.39)`:
`E[(Π̂^ε_x τ)(y)] = -2 ∫ K(x - w) Q_ε(w - y)² dw`, using that `Q_ε` is even and that
`C₂ = 2 ∫ K Q_ε²` (the definition of `hairerSunsetConstant`) in the form
`∫ K(y - w) Q_ε(w - y)² dw = ∫ K Q_ε² = C₂ / 2`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

                                                                   
                                                                                        
                                                                
                         
                                                                                   
                                     
                                                                    
                                                                                           
                                                            

                        
                                                                                      
                                                                                 
                                                               
                                                              
                                      
          

                                          
                                                                          
                                          
                                           

                                            
                                                                                         
                                                                                   
                                                                                                
                                                                       
                                                                                                
                                                               
                                                                                           
                                                                     
                                
                                                

                                                                
                                                                                 
                                                                                           
                                                                                   
                                         
                                                                       
                                          
                                                       
                                          
                                                                 
                                 
                                                 
                                                               
                                               
                                                                                                
                                                                                      
                                                                
                                                          
                                           
                                                             
                                                                                 
           
                                                                                     
                                                                                     
                                
                                                           
                                                                                
                      
                                                                             
                                     
                                                
                                                                   
                              
              
                                                                                                
          
                                                                               
           
                             
                                                                                     
                 
                                                                                  
                      
                 
                                                 
                                                                      
             
                 

                                                              
                                                        
                                                                                       
                     
                                                                               
                                      
                                            
                                                                     
                             
          
         
                                                                    
           
                                                    

                                                                 
                                                                                  
                                                                            
                                                                                   
                                                             
                                               
                                                                                        
                                 
                                                                            
                                           
                                                                      
                                                                      
                                                          
                                          
                          
                                               
                                                     
                                                                                            
                                                                              
                                                                                             
                             
        
                  
                                                                                             
       
      

end RegularityStructures.Phi43

end

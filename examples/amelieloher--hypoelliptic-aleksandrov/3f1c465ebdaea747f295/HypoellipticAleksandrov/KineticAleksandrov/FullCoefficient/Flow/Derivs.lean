module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Mass
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Coordinate derivatives of the Gaussian exponential

Directional derivatives of `gaussExp a b c = exp (-quadForm a b c)` along the coordinate
directions of phase space. A direction is `δ : Fin d ⊕ Fin d`: `inl i` is the velocity direction
`e_i` and `inr i` the position direction. The Leibniz rule
`∂_δ (p * G) = (∂_δ p - p * ∂_δ Q) * G` and the constancy of the second derivatives of `Q` are
the two inputs of the polynomial calculus used for the Gaussian flow estimates.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Real

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

                                                             
                                                           
                                                                    
                                                               

                                                        
                                                                    
                                        
                         

                                                                                   
                                                                                             

                                                                                   
                                                                                             

                                                                        
                                                           
                                                                                       

                                                                        
                                                           
                                                                                       

                                                                                                  
                                                                                                  

                                                                                               
def gen (a b c : ℝ) : Fin d ⊕ Fin d → EvolutionAmbientState d → ℝ
  | Sum.inl i, y => b * y.2 i + 2 * c * y.1 i
  | Sum.inr i, y => 2 * a * y.2 i + b * y.1 i

                                                             
                                                            
                                                      
                                                  
                                                  
                                                      

                                                                        
                                
                                                                                     
                                                
                 
                                          
                                            
                                            
                                                                                               
                      
            
                    
                                              
        
        

                                                                                           
                                                         
                   
                                            
                     
                                                               
        
                                                               
        

                                                        
                                                                     
                 
                                   
                                                                                          
                                                                                          
          

                                                        
                                                                  
                                                        

                                                                                       
                                                                          
                                                     
                     
                                                      
                                                                  
                                                             
                
                                                                          
                                                      
                                                                        
                                                       
                
                                                                          

                                                                                         
                                                             
                                                 
                   
                    

                                                            
                                                                            
                                                            

                                                                                           
                                                                             
                            
                                                          
                                                                    
                                                                                  
               
                                       
                           
             
      

                                                                                        
                                                               
                                                                   
                                   
                                                      
                                                                       
                                                                                  
                                                              
                   
                           
                                       
                           
             
      

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

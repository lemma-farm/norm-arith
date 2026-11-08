/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Jet
public import RegularityStructures.PDE.DuhamelTime

/-!
# Mild solutions with smooth data solve the equation pointwise

Let `G` be a smooth nonlinearity, `u₀` a smooth function on `T³` and `u` a continuous mild solution
of `∂_t u = Δu + G(t, x, u)`, `u(0) = u₀`, on `[0, T]`. Then `u(t)` has continuous first and
second partial derivatives `w(t)`, `w2(t)`, and for `t ∈ (0, T)`
`∂_t u(t, x) = Δu(t, x) + G(t, x, u(t, x))` with `Δu = Σᵢ w2ᵢᵢ` (`hasDerivAt_of_isMildSolution`).

The second derivatives come from the jet of the jet system (`exists_jet_of_isMildSolution` applied
twice). The time derivative combines `∂_t P_t u₀ = P_t Δu₀` with the time derivative of the
Duhamel integral, which needs the Laplacian of `x ↦ G(s, x, u(s, x))`; this is computed with the
chain rule from the jets.
-/

open scoped ContDiff

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

                                                 
                                                                 
                                                                                           
                                                
                                                         
                                                                         
                                                         
                                                                         
                                                                           
                             

                               
                                                                           
                                                                           
                                                                                                
       
     

                                                         
                                                               
                                                          
                                                                       
                                                                                  
                                                                             
                                                                                 
                                                                    
                         
                                                                                 
                                                                               
                                                                                            
                                              
                                                                        
                                                                                        
                                                                                                
                                                                   
                                                         
                                                         
                  
                                                                                    
                   
                                                                                  
                                    
                                                                                   
                                        
                                                                                     
                                                                    
                                         
                                                                                     
                                                                                   
                                                                                               
           
                              
                                                                
                                                                                  
                                                                                              
                                                                                           
               
                                                                                 
                                                                              
              
                                                                           
                                  
                                                       
                                           
                                                                     
                                                                                              
                                                                                      
                                                                                               
                
                                                           
                                                                       
                                                                                
                                                                       
                                                                     
                                            
                                                                                
              
                                                                                         
                                               
                                                                                    
                                                                                                
           
         
                  
                                             
                                                  
                                                         
                                                                                           
                                                    
                          
                                
                                                          
                                                 
                                  
                                                                                    
                        
                                                      
                                                             
                        
                                                                                              
                                               
             
                                                               
        
                   
                                      
                                                   
                 
     

end RegularityStructures.PDE

end

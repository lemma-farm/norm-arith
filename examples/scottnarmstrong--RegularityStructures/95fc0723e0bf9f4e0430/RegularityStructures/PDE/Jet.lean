/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Nonlin
public import RegularityStructures.PDE.MildDeriv
public import RegularityStructures.PDE.SpatialDeriv

/-!
# The jet of a mild solution

If `u` is a continuous mild solution of `∂_t u = Δu + G(t, x, u)` with a `C¹` nonlinearity and
`C¹` initial datum, then `u(t)` has continuous partial derivatives `w(t)`, and the pair `(u, w)` is
a mild solution of the jet system `∂_t J = ΔJ + jetNonlin G (t, x, J)` with initial datum
`(u₀, Du₀)` (`exists_jet_of_isMildSolution`). Iterating gives all higher spatial derivatives.
-/

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### Calculus rules for `HasTorusDeriv` -/

theorem HasTorusDeriv.add {g h : C(Torus3, E)} {Dg Dh : C(Torus3, Fin 3 → E)}
    (hg : HasTorusDeriv g Dg) (hh : HasTorusDeriv h Dh) : HasTorusDeriv (g + h) (Dg + Dh) := by
  intro y
  simpa [map_add] using (hg y).fun_add (hh y)

theorem HasTorusDeriv.neg {g : C(Torus3, E)} {Dg : C(Torus3, Fin 3 → E)}
    (hg : HasTorusDeriv g Dg) : HasTorusDeriv (-g) (-Dg) := by
  intro y
  simpa [map_neg] using (hg y).fun_neg

                                                                                             
                                                                             
                                               
                                                   
                                              
                                                                                           
                            
         
                                                                 
                                                                                         
                                                                                  
                                              
                                                                                    
                                             
                 
       
          
                                   

                                      
                                                                               
                                                                        
         
                                           
                                                                                           
                                      

                                                           

variable [CompleteSpace E] [CompleteSpace F]

                                                                     
                                                                  
                                                                                     
                                                                                     
                                                                                              
              
                                                                                              
              
               
               
       
                                                          
                                                          

                                                                                            
                                   
                                                                                          
                                                          
                                                            
                                                                            
                                                            
                                                                            
                                                                               
                               
                                                                            
                                                                            
                                                                                 
                                        
                        
                                                                                 
                                        
                        
               
               
       
                                                          
                                                          

                                                                               
                                                                     
                                                          
               

                                                                                                  
                                                                                                 
                                                                                
                                                                                       
                                                                                       
                                                                            
                                                           
                                                                                               
                                          
                                                                 
                                                                              
                                           
                                                                                            
                                               
                                                          
                                            
                                                        
                                                 
                                                                             
                                                                   
                                                                                             
            
                 
                                                                                     
               

end RegularityStructures.PDE

end

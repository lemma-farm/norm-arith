module

public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Coordinate derivatives on phase space

Phase-space points are `y = (v, z) : EvolutionAmbientState d`, velocity first, as in the terminal
solution operator. This module fixes the coordinate partial derivatives and the second-order
operators used throughout the full-coefficient Aleksandrov estimate: velocity and position partials,
the velocity Hessian contraction
`B : D_v² F`, the transport derivative `v · ∇_z F`, the two Laplacians and the mixed operator
`∇_z · ∇_v`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

                                                                                    
                                                                 
                                        
                                 

                                                                                    
                                                                 
                                        
                                 

                                                                               
                                                                                
                                        
                                                             

                                                            
                                                         
                                        
                                    

                                      
                                                                                            
                                                

                                      
                                                                                            
                                                

                                                             
                                                                                          
                                                

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

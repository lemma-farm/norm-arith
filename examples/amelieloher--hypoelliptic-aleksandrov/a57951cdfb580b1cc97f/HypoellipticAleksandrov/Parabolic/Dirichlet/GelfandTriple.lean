module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevExtensionality
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Density
public import Mathlib

/-!
# The spatial Gelfand triple

This module realizes the dual side of the spatial Gelfand triple
`H¹₀(Ω) → L²(Ω) → (H¹₀(Ω))^*`.  It uses the continuous, injective spatial
value map and its dense-range theorem, together with the real Hilbert-space pairing.

No coercivity, time-dependent, Bochner, or PDE assertion is made here.
-/

@[expose] public section

open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The `H⁻¹` carrier dual to the spatial Hilbert realization of `H¹₀(Ω)`. -/
abbrev H10HilbertGraphDual (hΩ : IsOpen Ω) : Type _ :=
  StrongDual ℝ (H10HilbertGraph hΩ)

                                                                            
                                               
                                               
                     
                                                             
                                              

       
                                           
                                                   
                              
                                                                          
                                                              
                           

                                                                                    
                                                   
                                                     
                                                                    
                                                    

                                                                                
                                               
                     
                                                               
               
                      
                                                   
                                                  
                                              
                                                                                   
                            
                                          
            
                       
               
                                            
                                               
                                                        
                                                                                            

end HypoellipticAleksandrov.Parabolic.Dirichlet

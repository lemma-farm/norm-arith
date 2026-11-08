module

public import SquaresInCircles.Common.Charts

/-!
# Charts of exterior squares in a disk

A sorted chart `(a, u)` of an exterior square whose far vertex lies in the
closed disk of squared radius `Q` has `1/2 ≤ a`, `0 ≤ u ≤ a` and `φ(a, u) ≤ Q`
(`ExteriorChart`). With a signed transverse coordinate `b`, `|b| = u`, the far
corner `(|a| + 1/2, |b| + 1/2)` lies in the disk and the centre `(a, b)` within
`√(Q - 1/4) - 1/2` of the disk centre.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

/-- The sorted chart `(a, u)` of an exterior square whose far vertex lies in the
closed disk of squared radius `Q`. -/
structure ExteriorChart (Q a u : ℝ) : Prop where
  half_le : 1/2 ≤ a
  u_nonneg : 0 ≤ u
  u_le : u ≤ a
  phi_le : phi a u ≤ Q

namespace ExteriorChart
variable {Q a u : ℝ} (h : ExteriorChart Q a u)
include h

                                                 

                                  
lemma containment : (a+1/2)^2+(u+1/2)^2 ≤ Q := h.phi_le

end ExteriorChart

                                                                
                                                                     
                                     
                               
                

                                                                             
                                                                          
                                             
                                                                                            
                 
                                                                                

                                                                                 
                                              
                                                                                          
                                                                                         
                              
                                                         

                                                                                            
                                                                                

                                                                         
                                                                           
                                                                       
                                                                                 
                  
                                     

                                                                          
                                             
                                                                                     
                                   
                                                                 
                                                        
                                                           
                                                                            

end SquaresInCircles

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Flow.IsFlow
public import AVenhance.Statements.Roots.IsZ2Periodic
public import AVenhance.Infra.Flow.CurveUniqueness
public import Mathlib

/-! Algebraic consequences of the global flow characterization. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Flow

/-- The global Lipschitz hypothesis makes an integral curve unique from one value. -/
theorem flow_eq_of_isFlow
    (b : ℝ → Vec 2 → Vec 2)
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {X Y : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X) (hY : AVenhance.IsFlow b Y) : X = Y := by
  rcases hL with ⟨L, hL⟩
  funext t
  funext x
  funext s
  have hcurves := integralCurve_unique b hL (fun r => hX.2 x s r)
    (fun r => hY.2 x s r) (s := s) (by rw [hX.1, hY.1])
  exact congrFun hcurves t

                                                            
                      
                           
                                                          
                                                           
                                                             
                        
                                                         
                                           
                                                                   
                          

                                                                                  
                                
                           
                                                          
                                                   
                                                           
                                           
                                                                                   
                        
                                   
                       
                                                                   
                                                                    
                              
                                                                   
                                           
                                                      
                          

                                                                                    
                           
                           
                                                          
                                            
                                                           
                                                               
                        
                       
                                               
                                           
                                                                           
                                                 
                                                                   
                                                                        
                   
                          

                                                                          
                            
                           
                                                           
                                                             
                                                                            

end AVenhance.Infra.Flow

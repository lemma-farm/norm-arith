/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyGeometry
public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGGeometry

/-! # Euclidean overlap bounds for multiscale boundary profiles

This module proves the geometric packing step behind the cross-scale energy
estimate: if a fine square neighborhood met two neighborhoods of separated
coarse squares, then the coarse squares would be too close.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The Euclidean norm on two coordinate differences satisfies the triangle
inequality. -/
private theorem sqrt_sum_sq_triangle (a b c d : ℝ) :
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := by
  let X := Real.sqrt (a ^ 2 + b ^ 2)
  let Y := Real.sqrt (c ^ 2 + d ^ 2)
  have hX : X ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [X]
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  have hY : Y ^ 2 = c ^ 2 + d ^ 2 := by
    dsimp [Y]
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg c) (sq_nonneg d))]
  have hXY : 0 ≤ X * Y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hdotSq : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a * d - b * c)]
  have hdot : a * c + b * d ≤ X * Y := by
    have habs : |a * c + b * d| ≤ X * Y := by
      calc
        |a * c + b * d| = Real.sqrt ((a * c + b * d) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt ((X * Y) ^ 2) := Real.sqrt_le_sqrt (by
          have hprod : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (X * Y) ^ 2 := by
            rw [← hX, ← hY]
            ring
          rw [← hprod]
          exact hdotSq)
        _ = X * Y := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hXY]
    exact (le_abs_self _).trans habs
  have hsquares :
      (a + c) ^ 2 + (b + d) ^ 2 ≤ (X + Y) ^ 2 := by
    nlinarith [hX, hY, hdot]
  calc
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤ Real.sqrt ((X + Y) ^ 2) :=
      Real.sqrt_le_sqrt hsquares
    _ = X + Y := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    _ = Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := rfl

                                                                    
                                                         
                                                                                           
                              
                                
                                                       
                                                       
                
                                                             
                                          
                
                                                             
                                          
                           
         

                                                        
                                                                                 
                                                                    

                                                                                       
                                        
                                                  
                                   

                                                                       
                                               
                                                     
                                         
                                                                                          
                                                                                            
                                                                             
                          
                                                                         
                              
                                                                          
                              
                          
                                                                         
                              
                                                                          
                              
                                                                       
                                       
                                                                         
                                
                                                                         
                                
                                                                          
                                
                                                            
                                  
        
                                                                
                                                                              
                                                                   
                                           
                                                          
                                                                   
                                                                         
                                                           
                                                                   
                                                                    
                                            
                                                          
                                                      
                          
                                                  
                                                           
                                                 

                                                                              
          
                                              
                                     
                                               
                                                  
                                            
                         
                                                                        
                              
                                                                        
                              
                                                                        
                                
      
                                                               
                                 
                                                                  
                                            
                                                 
                        

                                                                            
                                                   
                                                               
                                                   
                                                      
                                                                  
                             
                                                       
                                                                                          
                                                                                            
               
                                                                          
                 
                              
                                              
                                                       
        
                                            
                                                       
                                            
                                                             
                                           
                                                                                              
              
                                                
                                       
                                                     
             
                                                 
                                                        
          

end FroehlichSpencer.BKT.Generic.PinnedCharges

end

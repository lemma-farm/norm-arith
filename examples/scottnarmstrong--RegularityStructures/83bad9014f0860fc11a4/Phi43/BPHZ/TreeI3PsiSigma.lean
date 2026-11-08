/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiChainBasic

/-!
# Symmetrisation of the exponents `s(a - b)^(-δ)`

For the three points `z`, `z'`, `0`, every ordered pair `(a, b)` gives
`s(a - b)^(-δ) ≤ 2 (s(z - z')^(-δ) + s(z - 0)^(-δ) + s(z' - 0)^(-δ))`, using
`s(-x) ≤ 2 s(x)` and that `s(a - a) = 0`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem torusParabolicSize_zero_spaceTime : torusParabolicSize (0 : SpaceTime) = 0 := by
  unfold torusParabolicSize
  simp [torusSpatialNorm_zero]

/-- Positivity of `s(a - b)` is symmetric. -/
theorem torusParabolicSize_sub_pos_symm {a b : SpaceTime} (h : 0 < torusParabolicSize (a - b)) :
    0 < torusParabolicSize (b - a) := by
  have := torusParabolicSize_neg_le_two_mul (b - a)
  rw [neg_sub] at this
  linarith

                                                                    
                                                                               
                                                            
                                                                                   
                                                        
                      
                                                             
                                                                                          
                                                                   
                                                     
                                                     
                                                                                    
                         
              
                                 
                                                                                        
                              
                                                                            
                  
               
                                                                                 

                                                                              
                                                                                     
                                                                  
                                                                                   
                                                                 
                                                                                 
                                                                                   
                                                                                                      
                                                                                                     
                                                                                                      
                                                              
                                                              
                                                               
                                                                        
           
                                                    
                                               
                 
                  
                               
                                                                                          

end RegularityStructures

end

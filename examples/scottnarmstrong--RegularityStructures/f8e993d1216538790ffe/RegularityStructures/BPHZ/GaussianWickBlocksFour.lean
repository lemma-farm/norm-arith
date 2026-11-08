/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickBlocksPositions
public import RegularityStructures.BPHZ.GaussianWickMonomialSpecial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Four Wick monomials: the block patterns of the `Φ⁴₃` trees

For a centred Gaussian vector with covariance `C` and indices `a b c d`:

* `E[:X_a^3: X_b :X_c^3: X_d] = 18 C_ab C_ac² C_cd + 6 C_ac³ C_bd + 18 C_ac² C_ad C_bc`;
* `E[:X_a^2: :X_b^2: :X_c^2: :X_d^2:] = 4 C_ab² C_cd² + 4 C_ac² C_bd² + 4 C_ad² C_bc²
  + 16 (C_ab C_ac C_bd C_cd + C_ab C_ad C_bc C_cd + C_ac C_ad C_bc C_bd)`;
* `E[:X_a^3: :X_b^2: :X_c^3: :X_d^2:] = 36 C_ab² C_ac C_cd² + 72 C_ab C_ac² C_bd C_cd
  + 144 C_ab C_ac C_ad C_bc C_cd + 12 C_ac³ C_bd² + 72 C_ac² C_ad C_bc C_bd
  + 36 C_ac C_ad² C_bc²`.

Each pair of positions is oriented from the earlier block to the later one, so no symmetry of `C`
is needed.  The proofs evaluate the list recursion `listMatchSum` on the tagged letters.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

                                          
                                                                                       
                                  
                                                                                      
                                    
                                                                           
                                                                               
                                                  

                                             
                                                                                          
                       
                                                            
                                                              
                                                                                                   
                                                                                
                            
                                            
           
                                                                                            
                                 
      

                                                     
                                                                
                                                           
                                                                                                
                                                                                                  
                                                                                         
                                                                             
                                              
                                                    
                                                                                            
                                 
      

                                                     
                                                                    
                                                           
                                                                                                
                                                                                                  
                                                                                   
                                                                                  
                                                                                         
                                                    
                                                                                            
                                 
      

end RegularityStructures

end

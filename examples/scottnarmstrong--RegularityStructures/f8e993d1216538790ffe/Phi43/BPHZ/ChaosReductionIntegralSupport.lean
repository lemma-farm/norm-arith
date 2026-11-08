/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusBasic

/-!
# Support of the torus parabolic test function in the parabolic size

For `φ` in the test-function class, `lam > 0` and a base point `z`, the test function
`torusParabolicTestIoc φ lam z` is bounded by `lam⁻⁵` times the indicator of a measurable set `K`
of volume at most `16 lam⁵` on which `s(w - z) ≤ 3 lam`, where `s = torusParabolicSize`.

**Cell boundary.**  The test function is centred at the `(0, 1]`-representative of `z.2` and lives in
the box `torusBoxIoc`, which may straddle the boundary of the representative cell `(0, 1]³`.  The
torus parabolic size `s(w - z)` is computed from the centred representative of `w.2 - z.2` and is
bounded by the Euclidean norm of the difference of any two lifts
(`abs_torusCenteredRep_le_abs_of_torusProj`), in particular of the two `(0, 1]`-representatives.
Thus the bound `s(w - z) ≤ 3 lam` holds on the whole support, whether or not the box wraps around.
-/

public section

open MeasureTheory

namespace RegularityStructures

                                                           
                                                                             
                                                                            
                                         
                                                                 
                                             
                                                             
                                                                            
                                            
                                                                     
                                                                      
                             
                                
                                      
                                               
                                                
                                            
                                             
                                
                   
                    
                                                    

end RegularityStructures

end

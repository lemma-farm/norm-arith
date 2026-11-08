/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramZero
public import RegularityStructures.BPHZ.TreeI2Psi2DiagramAlg

/-!
# Chaos `4` of the tree `I(Ψ²) Ψ²`: deterministic bound

[Hai14, (10.39)-(10.42), p. 169].  See `abs_integral_chaos4_le`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem abs_le_one_of_torusParabolicSize_le_one {u : SpaceTime} (h : torusParabolicSize u ≤ 1) :
    |u.1| ≤ 1 := by
  by_contra hc
  have h1 : 1 < √|u.1| := by
    rw [Real.lt_sqrt zero_le_one]; norm_num; exact not_le.1 hc
  have h2 := torusSpatialNorm_nonneg u.2
  unfold torusParabolicSize at h
  linarith

                                                               
                                                                                                      
                                                                
                                               
              

                                                         
                                                                                               
                                                                                       
                                                                 
                                                                                            
                                                                                                
                                                                                             
                                        
                                        
                                                            
                         
                              
                       
                                                                      
                                                                                                  
                                                                     
                                                                                
                    

end RegularityStructures

end

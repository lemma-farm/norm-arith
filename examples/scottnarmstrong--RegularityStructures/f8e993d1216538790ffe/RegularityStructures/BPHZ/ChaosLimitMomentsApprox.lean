/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.MeasureTheory.Function.SimpleFuncDense
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite-range sampling maps

* `exists_sampling_sequence`: for a closed nonempty set `S` of space-time there are measurable maps
  `πₙ` with finite range inside `S` and `πₙ x → x` for all `x ∈ S` (from `SimpleFunc.approxOn`);
* `integral_mul_comp_eq_sum`: for a map `π` with values in a finite set `T`,
  `∫ a(x) f(π x) = ∑_{b ∈ T} f(b) ∫_{π ⁻¹ {b}} a`.
-/

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

                                                                                           
                                                                        
                                                              
                                                            
                                                         
                        
                                                                                                     
                                                                                       
            
                                                                         

variable {β : Type*} [MeasurableSpace β]

                           
                                                                                       
                                                                            
                                                                 
                                                                  
                                                                                         
           
                                     
              
                        
                       

                                                                                      
                           
                                                                                   
                                                                                
                                                                     
                                              
                                         
                                                               

                                                                                       
                                                                                        
                                                                                
                         
                                                                         
                                                                  
                                  
                                              
                                                                        
                                           
                                                    

end RegularityStructures

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.GeneratorScaling
public import RegularityStructures.Analysis.Kernel.GeneratorIdentity
public import RegularityStructures.Analysis.Semigroup.Pairing.Main

/-!
# Pairing against a reflected, supported function

For a smooth `h : ℝ⁴ → ℝ` vanishing outside the parabolic ball `‖w‖_𝔰 ≤ lam`, the function
`y ↦ h (x - y)` is supported in the ball of radius `lam` about `x`, has the same `L¹` norm as `h`,
and `L (h (x - ·)) = (L h) (x - ·)` (the generator has even order).  Hence the pairing bound
`abs_pairing_le` (Hairer, arXiv:1303.5113v4, (3.3) type estimate) applies to it
(`abs_pairing_reflect_le`).
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

                                                                                            
                              
                                                            
                                                                    
                                                                                                 
                                                                 
                                                                                         
                                                                
                                       
                                                                               
                                                                        
                                                                             
                                              
                                                         
                           

                                                                                  
                            
                                                                                  
                           
                                                                
          

                                                                                  
                                                                           
                                                                    
                                                                   
                                                                  
                                                       
                                             
                                                
                                                                                                     
                                                  
                                                                                            
                                
       
                           
                             
      

                                                                             
                                       
                                                                   
                                               
                                                               
                               
                                                                                          
                                                                                 
                  
                                                           

end RegularityStructures

end

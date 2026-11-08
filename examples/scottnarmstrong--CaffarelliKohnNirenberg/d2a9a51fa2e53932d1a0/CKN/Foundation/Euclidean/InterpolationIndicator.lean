-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.InterpolationBasic

/-!
# Moduli and Lebesgue integrals of indicator truncations

The Marcinkiewicz interpolation argument used for the Caffarelli–Kohn–Nirenberg
program (CKN 1982) splits a function into a high-frequency part, carried by a
superlevel set of the `ℝ≥0∞`-valued modulus `absE f x = ENNReal.ofReal |f x|`,
and a low-frequency part, carried by its complement.  Both parts are indicator
truncations `s.indicator f` of the original function.

This file records the three elementary identities needed for that bookkeeping.
The first states that `absE` commutes with truncation pointwise, so that
`absE (s.indicator f)` is the truncation of `absE f` and the modulus of a
truncated function vanishes off `s`.  The second and third state that the
Lebesgue integrals of `absE (s.indicator f)` and of its square over all of
`Vec3` agree with the corresponding integrals over `s` alone.  All three are
stated for an arbitrary measurable set `s` and an arbitrary function
`f : Vec3 → ℝ`; the two integral identities use the restriction of Lebesgue
measure to `s`.
-/

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

                                                                              
                                                                         
                                               
                                                       
                                                     
          
                                             
                                                
                     
                                                         
                                                               
        

                                                                                 
                                                             
                                                                                     
                                                            
                                                

                                                    
                                                 
                                                                                        
                                                                    
                                                    
                                              
                          
            
                       
                                                           
                                                                 
          
                                   

end CKN.Foundation.Euclidean

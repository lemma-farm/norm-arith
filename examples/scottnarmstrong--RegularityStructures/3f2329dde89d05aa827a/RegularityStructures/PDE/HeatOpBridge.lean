/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.HeatOp
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The heat operator is the heat semigroup of `RegularityStructures.Torus.HeatKernel`

For `t > 0` and `g ∈ C(T³)`, `heatOp t g = heatSemigroup t g`: the substitution `y = √t z` turns
`∫ γ_t(y) g(x - y) dy` into `∫ γ₁(z) g(x - √t z) dz`, because `γ₁(z) = t^{3/2} γ_t(√t z)`.

Consequently the facts proved for `heatOp` (joint continuity in `(t, g)`, `P_0 = id`, strong
continuity, commutation with translations, smoothing of derivatives, the heat equation) apply to
`heatSemigroup` for positive times.
-/

public section

open MeasureTheory Real

namespace RegularityStructures.PDE

                                             
                                                                 
                                                           
                                                   
                                                                                                
                                                                      
            
              
                                                                                        
                                         
                                                                                 
                                                               
            
                                                        

                                                   
                                                                                      
                                            
                                                                                   
                                                         
                                           
           
            
                                                 
        
                                         
                                                                                       
                                                                         
     

end RegularityStructures.PDE

end

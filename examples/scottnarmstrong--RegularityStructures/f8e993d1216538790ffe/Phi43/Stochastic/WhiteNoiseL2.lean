/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.WhiteNoiseLinearity

/-!
# The `L²` isometry identity for white-noise pairings

Almost-sure linearity of a Gaussian white-noise family gives the exact distance formula

`E |W h - W g|² = ∫ (h - g)²`.

This is the deterministic-to-annealed continuity interface used by heat-kernel approximations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

                                                         
                                                             
                                                  
                                          
                                               
                                   
            
                                
        
                                                           
                           
                                  
          

end RegularityStructures

end

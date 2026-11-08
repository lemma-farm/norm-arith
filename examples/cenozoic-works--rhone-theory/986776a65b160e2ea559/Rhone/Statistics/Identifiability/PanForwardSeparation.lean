/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.AbsolutelyContinuousClock
public import Mathlib
/-! # Separation from panmictic forward systems with measurable time variation -/

@[expose] public section

open scoped ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

structure PanForwardSystem where
  rate : ℝ → ℝ
  recombination : ℝ → ℝ
  clock : ℝ → ℝ
  firstFlux : ℝ → ℝ
  postMass : ℝ → ℝ → Fin 2 → ℝ
  rate_measurable : Measurable rate
  recombination_measurable : Measurable recombination
  clock_measurable : Measurable clock
  firstFlux_measurable : Measurable firstFlux
  rate_nonneg : ∀ t, 0 ≤ rate t
  recombination_nonneg : ∀ t, 0 ≤ recombination t
  firstFlux_nonneg : ∀ t, 0 ≤ firstFlux t
  initial_mass : ∀ s, 0 < s → (∑ i, postMass s s i) = 1
  post_nonneg : ∀ s t, 0 < s → s ≤ t → ∀ i, 0 ≤ postMass s t i
  post_ac : ∀ s t, 0 < s → s < t → ∀ i,
    AbsolutelyContinuousOnInterval (fun x => postMass s x i) s t
  clock_ac : ∀ s t, 0 < s → s < t → AbsolutelyContinuousOnInterval clock s t
  post_equation : ∀ s t, 0 < s → s < t → ∀ᵐ x, x ∈ uIcc s t → ∀ i,
    HasDerivAt (fun y => postMass s y i)
      (∑ j, postMass s x j * panPostGenerator (rate x) (recombination x) j i) x
  clock_equation : ∀ s t, 0 < s → s < t → ∀ᵐ x, x ∈ uIcc s t →
    HasDerivAt clock (rate x) x

                                                                                       
                                                    

                                                                        
                                
                                                                    
                                                                                       
                                                  
                                                              
                                                   

                                                                            
                                
                                                                             
                                                             
     

                                                            
                                                                 
                         
                                                         
                                                           
                              
                                                                            
                                                               
                                    
         
                            
                                                   
                         
                              
                                            
                               
                                                         

end Rhone.Statistics.Identifiability

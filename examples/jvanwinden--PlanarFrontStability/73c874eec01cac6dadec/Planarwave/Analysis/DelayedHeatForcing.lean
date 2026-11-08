/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.TemporalCutoff
public import Planarwave.Analysis.HeatSemigroup

@[expose] public section

/-!
# The delayed forcing of Section 4.2

The natural index `k` below represents the paper's positive integer `k+1`.
Only the preceding unit time interval enters each forcing pulse. The source
will be the adjoint projection of the front's nonlinear remainder.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The source accumulated during a single completed time block. -/
def delayedHeatBlock (a : ℝ) (N : ℝ → BUC E F) (k : ℕ) : BUC E F :=
  ∫ r in (k : ℝ)..(k : ℝ) + 1, heatFlowBUC a ((k : ℝ) + 1 - r) (N r)

/-- Equation `eq:defgnew`, including the initial-data pulse. -/
def delayedHeatForcing (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F) (t : ℝ) : BUC E F :=
  trackingCutoff t • heatFlowBUC a t p +
    ∑' k : ℕ, trackingCutoff (t - ((k : ℝ) + 1)) •
      heatFlowBUC a (t - ((k : ℝ) + 1)) (delayedHeatBlock a N k)

                                                                                 
                                                                          
                                                                             
                                         
                                                         
                                      
                   
                                                         
                                      
                   

                                                                                      
                                                                          
                          
                                                                           
                                                                
                                                                                  
                                                                       

                                                                       
                                                                                        
                                                                   
                                                                                                 

                                                                       
                                                                            
theorem delayedHeatForcing_eq_sum (a : ℝ) (p : BUC E F) (N : ℝ → BUC E F)
    (K : ℕ) {t : ℝ} (ht : t ≤ (K : ℝ) + 1) :
    delayedHeatForcing a p N t = trackingCutoff t • heatFlowBUC a t p +
      ∑ k ∈ Finset.range K, trackingCutoff (t - ((k : ℝ) + 1)) •
        heatFlowBUC a (t - ((k : ℝ) + 1)) (delayedHeatBlock a N k) := by
  unfold delayedHeatForcing
  congr 1
  apply tsum_eq_sum
  intro k hk
  have hkn : K ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
  have hcast : (K : ℝ) ≤ k := by exact_mod_cast hkn
  rw [trackingCutoff_eq_zero_of_le (by linarith : t - ((k : ℝ) + 1) ≤ 1 / 4), zero_smul]

                                                                          
                                                                        
                                              
                                                
                                                                       
                                                      
                                                                                         
                                                     
                                                                                       
                  

                                                                            
                                                                  
                                                
                                                         
                                       
            
                                                             
            
           

                                                                       
                                                           
                                                                           
                                            
                                          
                                                                                         
              
                                                                                      
             
                                                                  
                                                                                    
                                              

                                                                                      
                                                                          
                                                       
                                      
                                             
                                                       
              
                                                               
                                                                  
                                                                            
                                                         

                                                                                  
                          
                                                               
                                                                       
                                            
                                                                                       

                                                                                
                                                                                
                                              
                                                       
                                                                             
                                                                       
                                            
                                 
                                                                           
                             

end

end Planarwave

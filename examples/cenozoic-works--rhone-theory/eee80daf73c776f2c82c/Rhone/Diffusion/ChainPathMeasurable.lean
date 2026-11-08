/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.ChainIncrements
public import Rhone.Diffusion.PathModulus
public import Rhone.Probability.ContinuousPathMoments
public import Mathlib
/-! # Measurability of rescaled chain paths and the fourth moment of one step -/

@[expose] public section

namespace Rhone

open MeasureTheory Filter Set Analysis MarkovChain Probability
open scoped NNReal

variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]

                                                                                 
                                                       
                                                                               
                                                                        
                                             
                                                                                                  
                                                               
                                    
                                                                            
                                   
                                                        

                                                                                        
                                                       
                                                                       
                                                                          
                                                                    
                                                                   
        
                                                         

                                                              
                                                                             
                                                                                              

                                                               
                                                                               
                                                                                                 
          
                                                                     
            
                                                                                       
                                 
                                         
            
                            
            

namespace MarkovChain.FinChain

variable [Fintype S] (C : FinChain S)

theorem integral_step_pow_four_le (g : S → ℝ) {q : ℝ}
    (hq : ∀ z, C.expect (fun w => (g w - g z) ^ 4) z ≤ q) (x : S) (l : ℕ) :
    ∫ ω, (g (ω (l + 1)) - g (ω l)) ^ 4 ∂C.pathLaw x ≤ q := by
  have h1 := C.integral_mul_eval_succ_two x l (fun a b => (g b - g a) ^ 4)
    (h := fun _ => (1 : ℝ)) stronglyMeasurable_const (B := 1) (fun _ => by simp)
  simp only [one_mul] at h1
  rw [h1]
  have hi : Integrable (fun ω : ℕ → S => C.expect (fun w => (g w - g (ω l)) ^ 4) (ω l))
      (C.pathLaw x) := C.integrable_eval (fun z => C.expect (fun w => (g w - g z) ^ 4) z) l x
  calc ∫ ω, C.expect (fun w => (g w - g (ω l)) ^ 4) (ω l) ∂C.pathLaw x
      ≤ ∫ _ω, q ∂C.pathLaw x := integral_mono hi (integrable_const q) fun ω => hq (ω l)
    _ = q := by simp

                                                              
                                                                                
                                                                 

end MarkovChain.FinChain

end Rhone

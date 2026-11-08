-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Flow.GlobalExistence
public import AVenhance.Infra.Flow.PeriodicSmooth
public import AVenhance.Infra.Flow.Continuity
public import Mathlib.Analysis.Calculus.MeanValue

/-! Consequences of compact-cell derivative bounds for smooth periodic fields. -/

@[expose] public section

open Homogenization
open scoped NNReal Topology

namespace AVenhance.Infra.Flow

/-- The spatial slices of a smooth jointly periodic field have a common global
Lipschitz constant. -/
theorem exists_global_spatial_lipschitz
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨L, hL, hbound⟩ := exists_global_iteratedFDeriv_bound hb 1
  let K : ℝ≥0 := ⟨L, hL⟩
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  have hdiff : Differentiable ℝ F := by
    exact hb.smooth.differentiable (by simp)
  have hderiv : ∀ p, ‖fderiv ℝ F p‖₊ ≤ K := by
    intro p
    have hp := hbound p
    rw [norm_iteratedFDeriv_one] at hp
    change ‖fderiv ℝ F p‖₊ ≤ K
    exact_mod_cast hp
  have hLip : LipschitzWith K F :=
    lipschitzWith_of_nnnorm_fderiv_le hdiff hderiv
  refine ⟨L, hL, ?_⟩
  intro t x y
  have h := hLip.dist_le_mul (t, x) (t, y)
  change dist (b t x) (b t y) ≤ (K : ℝ) * dist (t, x) (t, y) at h
  calc
    ‖b t x - b t y‖ = dist (b t x) (b t y) := by rw [dist_eq_norm]
    _ ≤ (K : ℝ) * dist (t, x) (t, y) := h
    _ = L * ‖x - y‖ := by
      rw [dist_eq_norm, Prod.norm_def]
      simp only [Prod.fst_sub, sub_self, norm_zero, max_eq_right (norm_nonneg _)]
      rfl

                                                                                                    
                                        
                                                          
                                                            
                                                
                              
                                                             
                 

                                                                        
                                                                        
                                               
                                                        
                                                             
                                                                 
                                                         
                                     

                                                         
                                     
                                              
                                                        
                                                             
                                                                         
                                                             
                                                               

end AVenhance.Infra.Flow

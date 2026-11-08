/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Tactic

/-! # Stable finite convex representations -/

@[expose] public section

open Set Filter
open scoped Topology BigOperators

namespace Rhone.Algebra.FinitePanelGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_pos_half_norm_lt_apply (f : E →L[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ y : E, ‖y‖ < 1 ∧ ‖f‖ / 2 < f y := by
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  obtain ⟨y, hy, hfy⟩ := f.exists_lt_apply_of_lt_opNorm (by linarith : ‖f‖ / 2 < ‖f‖)
  by_cases h : 0 ≤ f y
  · exact ⟨y, hy, by simpa only [Real.norm_eq_abs, abs_of_nonneg h] using hfy⟩
  · refine ⟨-y, by simpa using hy, ?_⟩
    simpa only [map_neg, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge h)] using hfy

theorem ball_subset_convexHull_of_vertex_perturbation {ι : Type*} [Finite ι]
    (p q : ι → E) (m : E) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball m r ⊆ convexHull ℝ (range p))
    (hclose : ∀ i, ‖q i - p i‖ ≤ r / 4) :
    Metric.ball m (r / 4) ⊆ convexHull ℝ (range q) := by
  classical
  have hm : m ∈ convexHull ℝ (range p) := hball (Metric.mem_ball_self hr)
  obtain ⟨_, ⟨i, rfl⟩⟩ := convexHull_nonempty_iff.mp ⟨m, hm⟩
  intro x hx
  by_contra hout
  obtain ⟨f, a, hsep, hax⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (range q)) ((finite_range q).isClosed_convexHull ℝ) hout
  have hf : f ≠ 0 := by
    intro hzero
    have hi := hsep (q i) (subset_convexHull ℝ (range q) (mem_range_self i))
    simp only [hzero, zero_apply] at hi hax
    linarith
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hp : ∀ j, f (p j) ≤ f x + ‖f‖ * (r / 4) := by
    intro j
    have hj := (hsep (q j) (subset_convexHull ℝ (range q) (mem_range_self j))).trans hax
    have he : f (p j) - f (q j) ≤ ‖f‖ * (r / 4) := by
      calc
        f (p j) - f (q j) = f (p j - q j) := (map_sub f _ _).symm
        _ ≤ ‖f (p j - q j)‖ := le_abs_self _
        _ ≤ ‖f‖ * ‖p j - q j‖ := f.le_opNorm _
        _ ≤ ‖f‖ * (r / 4) := by
          gcongr
          simpa only [norm_sub_rev] using hclose j
    linarith
  have hh : convexHull ℝ (range p) ⊆ {z | f z ≤ f x + ‖f‖ * (r / 4)} := by
    apply convexHull_min
    · rintro _ ⟨j, rfl⟩
      exact hp j
    · exact convex_halfSpace_le f.toLinearMap.isLinear _
  obtain ⟨y, hy, hfy⟩ := exists_pos_half_norm_lt_apply f hf
  have hz : m + r • y ∈ Metric.ball m r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hbound := hh (hball hz)
  change f (m + r • y) ≤ f x + ‖f‖ * (r / 4) at hbound
  rw [map_add, map_smul, smul_eq_mul] at hbound
  have hxm : f x - f m < ‖f‖ * (r / 4) := by
    calc
      f x - f m = f (x - m) := (map_sub f _ _).symm
      _ ≤ ‖f (x - m)‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖x - m‖ := f.le_opNorm _
      _ < ‖f‖ * (r / 4) := by
        apply mul_lt_mul_of_pos_left _ hn
        simpa only [Metric.mem_ball, dist_eq_norm] using hx
  nlinarith

                                                              
                                                                      
                                                          
                                                 
                                                                                   
                                               
                                                              
                                                                                            

                                                                   
                                                      
                                                
                                                      
                                                              
                                                                 
                                                   
           
                                                         
                                                            
                                                    
                                               
                                                         
                                          

                                                                
                                                              
                                                                                     
           
                                                                    
                                     
                                                                                         
           
                                                                     
                                                                            
                           
                           
                                           
                                                       
                
                                                           
                                      
              
                                                 
                  
                        
                       
                                           
                                 

                                                                        
                                                   
                                                                 
                                                            
                                                   
           
                                
                                           
                              
                                                          
                                      
                                               
                                   
                                                       
                                                              
               
                                                            
                                           
                   
        
                                                 
                                                                         
                                                                   
                                                                                   
              
                                       
                                          
                                                           
                                
               
                        
                                                

                                                                             
                                                              
                                                
                                                          
                                                                             
                                                                         
                                                   
                                                                         
                                                                     

                                                                            
                                                   
                                                
                                                          
                                                                             
                                                                         
                                                   
           
                                                            
                                                                       
                        
                                                                 
                                             
       
                                                                            
                
                                                               
                                                                                   
                                                      
                                                
            
                          
                            

end Rhone.Algebra.FinitePanelGeometry

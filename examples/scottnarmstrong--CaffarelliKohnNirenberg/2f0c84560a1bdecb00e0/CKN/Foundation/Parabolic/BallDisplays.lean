-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The parabolic ball and its volume

This file records the literal displays of `paper/ckn.tex` that describe the
open parabolic ball `𝔅_r(z)` of the metric `dpar` (equation
`eq:parabolic-ball` and Lemma `lem:parabolic-metric`):

* `𝔅_r(z) = B_r(x) × (t - r², t + r²)` for `z = (x, t)`;
* `C_r(z) ⊆ 𝔅_r(z)` and `𝔅_r(z) ⊆ C_{2r}(x, t + r²)`, where `C_r(z)` is the
  parabolic cylinder `B_r(x) × (t - r², t]`;
* `|𝔅_r(z)| = (8π/3) r⁵`.

The spatial ball `vec3Ball x r` uses the Euclidean norm on `Fin 3 → ℝ`
(`vec3EuclideanNorm`), so its volume is computed by transporting Mathlib's
volume of the Euclidean ball in `EuclideanSpace ℝ (Fin 3)` along the
measure-preserving equivalence `WithLp.toLp 2`.
-/

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Equation `eq:parabolic-ball`: the open `parabolicDist`-ball of radius `r`
about `z = (x, t)` is the product of the Euclidean ball `vec3Ball x r` with the
open time interval `(t - r², t + r²)`. -/
theorem metricBall_eq_parabolicBall (z : ParabolicPoint) (r : ℝ) :
    Metric.ball z r = vec3Ball z.1 r ×ˢ Ioo (z.2 - r ^ 2) (z.2 + r ^ 2) := by
  ext p
  change dist p z < r ↔
    vec3EuclideanNorm (p.1 - z.1) < r ∧ (z.2 - r ^ 2 < p.2 ∧ p.2 < z.2 + r ^ 2)
  rw [dist_eq_parabolicDist]
  change max (vec3EuclideanNorm (p.1 - z.1)) (Real.sqrt |p.2 - z.2|) < r ↔
    vec3EuclideanNorm (p.1 - z.1) < r ∧ (z.2 - r ^ 2 < p.2 ∧ p.2 < z.2 + r ^ 2)
  rcases le_or_gt r 0 with hr | hr
  · constructor
    · intro h
      exact absurd h (not_lt.mpr <| calc
        r ≤ 0 := hr
        _ ≤ vec3EuclideanNorm (p.1 - z.1) := vec3EuclideanNorm_nonneg _
        _ ≤ max (vec3EuclideanNorm (p.1 - z.1)) (Real.sqrt |p.2 - z.2|) := le_max_left _ _)
    · rintro ⟨hspace, -⟩
      exact absurd hspace (not_lt.mpr (le_trans hr (vec3EuclideanNorm_nonneg _)))
  · rw [max_lt_iff, Real.sqrt_lt' hr, abs_lt]
    constructor
    · rintro ⟨hspace, hlo, hhi⟩
      exact ⟨hspace, by linarith only [hlo], by linarith only [hhi]⟩
    · rintro ⟨hspace, hlo, hhi⟩
      exact ⟨hspace, by linarith only [hlo], by linarith only [hhi]⟩

                                                                              
                                                                            
                                                                        
                                      
                                                                                   
                                                                      
            
                                  
                                                                                  
                                                                     
                      
                                                                     

                                                                               
                                                           
                                
theorem metricBall_subset_parabolicCylinder_doubled (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) :
    Metric.ball z r ⊆ parabolicCylinder z.1 (z.2 + r ^ 2) (2 * r) := by
  intro p hp
  rw [metricBall_eq_parabolicBall] at hp
  change vec3EuclideanNorm (p.1 - z.1) < r ∧ (z.2 - r ^ 2 < p.2 ∧ p.2 < z.2 + r ^ 2)
    at hp
  change vec3EuclideanNorm (p.1 - z.1) < 2 * r ∧
    ((z.2 + r ^ 2) - (2 * r) ^ 2 < p.2 ∧ p.2 ≤ z.2 + r ^ 2)
  exact ⟨lt_of_lt_of_le hp.1 (by linarith only [hr]),
    by linarith only [hp.2.1, sq_pos_of_pos hr], le_of_lt hp.2.2⟩

                                                                             
                                                                             
                                                                              
                                                                        
                                    
                                    
                                                                   
                                  
                                           
                                                              
         
                                                                               
                               
                                                            
                                         
                                                                             

                                                                               
                                                                        
                                              
                                             
                           
                                                                   
                                            

                                                                            
                                                                          
                                                                     
                                                                             
                                  
                                                                    
                                                           
                                            
                                                             
                                                           
                              
                                                                               
         
      

end CKN.Foundation.Parabolic

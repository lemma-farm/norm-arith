/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.SiteToPlane
public import Critical2DKPZ.RandomWalk.Port.Walk.GaussianFourier
public import Critical2DKPZ.RandomWalk.Port.Walk.SRW
import Mathlib

/-!
# Gaussian normalization and parity bridges in dimension two

The product Gaussian at time `t` has coordinate variance `t/2`, hence equals
the heat kernel at time `t/2`. Graph distance has coordinate-sum parity.
-/

@[expose] public section

namespace Critical2DKPZ

/-- The squared Euclidean norm of a lattice site is the sum of coordinate squares. -/
theorem norm_siteToPlane_sq (z : Site) :
    ‖siteToPlane z‖ ^ 2 = (z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

                                                                            
                                                                   
                                                                                       
                                           
                        
                                                                  
                   
                          
                                                      
      
                                                                                       
                                                
                                                    
                                                   
                                                    
                                                                         
                                   
                                                                           
                          
             
          

                                                                           
                                                                                 
                                                           
                                                        
                      
                                                                     
                                                      
                                                                                  
                                                            
                                                                                             

                                                       
theorem norm_siteToPlane_sq_le_graphNorm_sq (z : Site) :
    ‖siteToPlane z‖ ^ 2 ≤ (LatticeProb.graphNorm z : ℝ) ^ 2 := by
  rw [norm_siteToPlane_sq, LatticeProb.graphNorm, Fin.sum_univ_two]
  push_cast
  have hc0 : ((z 0).natAbs : ℝ) = |(z 0 : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hc1 : ((z 1).natAbs : ℝ) = |(z 1 : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hc0, hc1]
  nlinarith only [sq_abs (z 0 : ℝ), sq_abs (z 1 : ℝ),
    mul_nonneg (abs_nonneg (z 0 : ℝ)) (abs_nonneg (z 1 : ℝ))]

/-- Absorbing the fixed four-step shift in the Gaussian denominator. -/
theorem gaussian_exponent_le {A B t : ℝ} (ht : 1 ≤ t) (hB : 0 ≤ B) (hBA : B ≤ A) :
    -A / (8 * (t + 4)) ≤ -(1 / 40 : ℝ) * B / t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [div_le_div_iff₀ (by positivity) ht0]
  nlinarith only [mul_nonneg hB (sub_nonneg.mpr ht),
    mul_nonneg (sub_nonneg.mpr hBA) ht0.le]

end Critical2DKPZ

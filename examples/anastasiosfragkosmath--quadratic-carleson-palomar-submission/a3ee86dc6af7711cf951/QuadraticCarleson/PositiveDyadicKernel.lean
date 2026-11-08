/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import QuadraticCarleson.Bohr
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# The dyadic kernels used in the positive estimate

This file records the elementary, exact part of the dyadic decomposition of
the quadratic Hilbert kernel.  The quotient defining a dyadic piece is given
the value zero at the origin; this is not an arbitrary extension, since the
numerator vanishes on a whole neighbourhood of the origin.
-/

open Function Set
open scoped ContDiff Topology

namespace QuadraticCarleson

/- The bump supplied by `ContDiffBump` is one on the inner closed ball and is
supported in the outer open ball.  With these radii those balls are exactly
the two intervals required in the paper. -/
noncomputable def dyadicCutoffData : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

noncomputable def dyadicCutoff : ℝ → ℝ := dyadicCutoffData

theorem dyadicCutoff_smooth : ContDiff ℝ ∞ dyadicCutoff := by
  exact dyadicCutoffData.contDiff

                                                            
         
                              

                                                              
                               

                                                              
                               

theorem dyadicCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1 / 4) :
    dyadicCutoff x = 1 := by
  apply dyadicCutoffData.one_of_mem_closedBall
  simpa [dyadicCutoffData, Metric.mem_closedBall, Real.dist_eq] using hx

theorem dyadicCutoff_eq_zero {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    dyadicCutoff x = 0 := by
  apply dyadicCutoffData.zero_of_le_dist
  simpa [dyadicCutoffData, Real.dist_eq] using hx

                                     
                                                         
                                               
                                  
            
                                    
                                                                    
                    
                          

                                                    
noncomputable def dyadicPsi (j : ℤ) (t : ℝ) : ℝ :=
  if t = 0 then 0 else
    (dyadicCutoff (2⁻¹ ^ j * t) - dyadicCutoff (2⁻¹ ^ (j - 1) * t)) / t

theorem dyadicPsi_eq_quotient {j : ℤ} {t : ℝ} (ht : t ≠ 0) :
    dyadicPsi j t =
      (dyadicCutoff (2⁻¹ ^ j * t) - dyadicCutoff (2⁻¹ ^ (j - 1) * t)) / t := by
  simp [dyadicPsi, ht]

theorem dyadicPsi_zero (j : ℤ) : dyadicPsi j 0 = 0 := by
  simp [dyadicPsi]

theorem dyadicPsi_eq_zero_of_abs_le {j : ℤ} {t : ℝ}
    (ht : |t| ≤ 2 ^ (j - 3 : ℤ)) : dyadicPsi j t = 0 := by
  by_cases ht0 : t = 0
  · simp [ht0, dyadicPsi]
  · rw [dyadicPsi_eq_quotient ht0]
    have hscale : |(2⁻¹ : ℝ) ^ (j - 1) * t| ≤ 1 / 4 := by
      rw [abs_mul, abs_zpow]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      norm_num
      calc
        (1 / 2 : ℝ) ^ (j - 1) * |t| ≤
            (1 / 2 : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j - 3) :=
          mul_le_mul_of_nonneg_left ht
            (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)) _))
        _ = 1 / 4 := by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
          rw [inv_zpow, ← zpow_neg]
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring_nf
          norm_num
    have hscale' : |(2⁻¹ : ℝ) ^ j * t| ≤ 1 / 4 := by
      rw [abs_mul, abs_zpow]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      norm_num
      calc
        (1 / 2 : ℝ) ^ j * |t| ≤
            (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ (j - 3) :=
          mul_le_mul_of_nonneg_left ht
            (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)) _))
        _ = 1 / 8 := by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
          rw [inv_zpow, ← zpow_neg]
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring_nf
          norm_num
        _ ≤ 1 / 4 := by norm_num
    rw [dyadicCutoff_eq_one hscale, dyadicCutoff_eq_one hscale']
    simp

theorem dyadicPsi_contDiffAt (j : ℤ) (t : ℝ) :
    ContDiffAt ℝ ∞ (dyadicPsi j) t := by
  by_cases ht : t = 0
  · subst t
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hball : Metric.ball (0 : ℝ) (2 ^ (j - 3 : ℤ)) ∈ 𝓝 0 :=
      Metric.ball_mem_nhds _ (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
    filter_upwards [hball] with u hu
    apply dyadicPsi_eq_zero_of_abs_le
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hu)
  · let q : ℝ → ℝ := fun u ↦
      (dyadicCutoff ((2⁻¹ : ℝ) ^ j * u) -
        dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * u)) / u
    have hq : ContDiffAt ℝ ∞ q t := by
      apply (ContDiffAt.sub ?_ ?_).div contDiffAt_id ht
      · exact dyadicCutoff_smooth.contDiffAt.comp t
          (contDiffAt_const.mul contDiffAt_id)
      · exact dyadicCutoff_smooth.contDiffAt.comp t
          (contDiffAt_const.mul contDiffAt_id)
    apply hq.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds ht] with u hu
    exact dyadicPsi_eq_quotient hu

theorem dyadicPsi_smooth : ∀ j : ℤ, ContDiff ℝ ∞ (dyadicPsi j) := by
  intro j
  rw [contDiff_iff_contDiffAt]
  exact dyadicPsi_contDiffAt j

theorem dyadicPsi_support_subset (j : ℤ) :
    support (dyadicPsi j) ⊆ {t : ℝ | 2 ^ (j - 3 : ℤ) < |t| ∧
      |t| < 2 ^ (j - 1 : ℤ)} := by
  intro t ht
  have ht0 : t ≠ 0 := by
    intro h
    exact ht (by simp [h, dyadicPsi])
  have hinner : 2 ^ (j - 3 : ℤ) < |t| := by
    by_contra h
    exact ht (dyadicPsi_eq_zero_of_abs_le (le_of_not_gt h))
  have houter : |t| < 2 ^ (j - 1 : ℤ) := by
    by_contra h
    have hlarge : 2 ^ (j - 1 : ℤ) ≤ |t| := le_of_not_gt h
    have hfirst : 1 / 2 ≤ |(2⁻¹ : ℝ) ^ j * t| := by
      rw [abs_mul, abs_zpow]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      calc
        (1 / 2 : ℝ) = (2⁻¹ : ℝ) ^ j * (2 : ℝ) ^ (j - 1) := by
          rw [inv_zpow, ← zpow_neg]
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring_nf
          norm_num
        _ ≤
            (2⁻¹ : ℝ) ^ j * |t| :=
          mul_le_mul_of_nonneg_left hlarge
            (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2⁻¹) _))
    have hsecond : 1 / 2 ≤ |(2⁻¹ : ℝ) ^ (j - 1) * t| := by
      rw [abs_mul, abs_zpow]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      calc
        (1 / 2 : ℝ) ≤ 1 := by norm_num
        _ = (2⁻¹ : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j - 1) := by
          rw [inv_zpow, ← zpow_neg]
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring_nf
          norm_num
        _ ≤
            (2⁻¹ : ℝ) ^ (j - 1) * |t| :=
          mul_le_mul_of_nonneg_left hlarge
            (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2⁻¹) _))
    have hzero : dyadicPsi j t = 0 := by
      rw [dyadicPsi_eq_quotient ht0]
      rw [dyadicCutoff_eq_zero hfirst, dyadicCutoff_eq_zero hsecond]
      simp
    exact ht hzero
  exact ⟨hinner, houter⟩

                                                                
         
                     
                        
                                                                             
                                                                     
                                           
                                             
                                                           
                       

                                          

                                                                           
                                                                 
                                                                           
  

                                                                    
                                                            
                                               
                                                     

                                                                       
                                                                                         
                                                     
                   
               
                                      
                                                        
                                                   
                                                                   
                                      
                                                 
                                                              
                      
                                                     
                                                   
               
                                      
                                                        
                                                   
                                                                   
                                      
                                                 
                                                              
                      
                                                     
                                                   

                                                                            
                                             
                                                                              
                                                
                                                                     
                                                                           
                           
                                                      
                                                        
               
                            
                                                                          
                                                 
                                                    
                                                  
                                           
                   
               
                                                                         

                                                                        
                                                                          
                         
                                                                                 
                                                                 

                                                                       
                                                                    
                                                                          

                                                                       
                                                 
                                           
                                                                        

                                                                              
                                                                       
                                            
                                                
                                                 
                                               
                                                  
               
                                                              
                     
                                                              
                     
                                   
                                                       

                                                                            
        
                                                                         
                                      
                                                
                  
                
                
                                         
               
          

                                                                    
                                       
                                                          
                                              
                                                                       
                                                     
                                               
                                                                     
                                                                           
                                                  
             
                                                
        
                                                     
                                                                
                
                                                         
                                                                               
                                                            
                               
                                                  
                
            
                                       
                                                
        
                             
                                                            
                                   
                                                         
                                    
                                                  
                
            
                                  
                                                  
                                               

                                                                             
                                                                           
                              
                                                                                   
                             
                                                 

                                                        
                                         
                                                                      
                                            
                           
                          
            
                                       
                                          
           

                                                                           
                                            
                                                                 
            
                
          
                                                        
            
                
            
                                                         

                                                        
                                   
                                        
                                              
                                              
                                                    
                                                    
             
                                                                               
        
                                                                       
                                        
                                                    
                                    
                     
                                        
                                                
                                      
                                                  
                                               
                          
                                                        

                                                                  
                          
                                                                    
                           
      
                                
                                                        
                                   
                                                            
                     
                                                    
                             
                
                                                                             
                                      
                                     
                                                         

                                                                                   
                                            
                                 
                                          
                                        
            
                                           
                                                    
                                                                     

                                                                          
                                                                          
                                                                        
                                                     
                                                         
                                                         
                  
                
                
                                                              
               
             

                                                                           
                         
                                           
                                                     
                                                                         

                                                                          
                                    
                                                     
                                                             
                                            
                     
                                                                          
                    
                                                                                   
                                 
                                                      
             
                                  
                                                                                       
                                   
                                                                          
                                     
                              
              
                                     
                             
         
           
                                   
                                                         
           
         

                                         
                                                             
                                                                            
                                       

                                                                             
                    
                                                 
                                                             
                                                            
                                                              
                                                                                
                                
                                                                  
                                
                                                                  
                                
                                                            
                                
                                                            
             
                   
                                                                          
                    
                                                                             
               
                            
                                                      

                                                 
                                                
                                                                
                     
             
                                                      
        
                                                                         
                                 
                                                                              
                            

                                                        
                                        
                                                    
                                 
                
                                                                
                                                                     
                                                         
                                              

                                                                           
                                                               
                      
                                                    
                                        
                                                    
                                                    
                                                  
            
                                           
                                              
                                                    
                                                                
                                                                             
             
        
                                                          
                                       
                                                                     
             
                                          
                                                                

end QuadraticCarleson

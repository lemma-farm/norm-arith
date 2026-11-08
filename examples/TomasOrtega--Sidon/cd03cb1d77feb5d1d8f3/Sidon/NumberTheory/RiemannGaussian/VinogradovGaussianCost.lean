module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianBounds
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
public import Sidon.NumberTheory.RiemannGaussian.VinogradovRectangleResonance
public import Sidon.NumberTheory.RiemannGaussian.VinogradovResonanceScaling

@[expose] public section

namespace RiemannGaussian.VinogradovGaussianCost
noncomputable section
open scoped BigOperators

theorem half_le_tail_denominator : (1 / 2 : ℝ) ≤ 1 - Real.exp (-Real.pi) := by
  have hp : (2 : ℝ) ≤ Real.exp Real.pi := by
    have h := Real.add_one_le_exp Real.pi
    linarith only [h, Real.pi_gt_three]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  rw [Real.exp_neg, inv_eq_one_div]
  linarith only [h]

theorem scalar_prefactor_le {k r : ℕ} (hk : k ≤ r) (hr : 1 ≤ r) :
    (2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
      (2 * (r : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ)) ≤ 48 * (r : ℝ) ^ 2 := by
  have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hkr : (k : ℝ) ≤ r := by exact_mod_cast hk
  have hden := half_le_tail_denominator
  have hden0 : 0 < 1 - Real.exp (-Real.pi) := by linarith only [hden]
  have hG : 2 * (r : ℝ) / (1 - Real.exp (-Real.pi)) ≤ 4 * (r : ℝ) := by
    apply (div_le_iff₀ hden0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hden (show (0 : ℝ) ≤ r by positivity)]
  have hterm : 2 * Real.pi * (k : ℝ) / (r : ℝ) ≤ 8 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hrr)).mpr
    have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (show (0 : ℝ) ≤ k by positivity)
    nlinarith only [hp, hkr]
  have hF : 2 * (r : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ) ≤ 12 * (r : ℝ) := by
    linarith only [hterm, hrr]
  calc
    _ ≤ (4 * (r : ℝ)) * (12 * (r : ℝ)) := mul_le_mul hG hF (by positivity) (by positivity)
    _ = _ := by ring

                                                      
                        
                                                              
                                                                                    
                      
                                                                   
                                                           
                                                            
                                       
                                            
                  
             
                                                 
                                               
                                                                  
                      
                                                                                                      
                                             
                                                             
                                                    
                                                                   
      
                                               
                                                                  
                         
                                                                    
               
                                                                                       
             
           

                                                             
                        
                                      
                                                                 
                                                                   
                                 
                      
                                             
                                                                      
        
                                                     
                                                                    
                           
                                                                              
                                                             
                                                        
                                                                  
                                        
                                               
                                      
                     
      
                                                      
                                                                                           
                                                                     
               
                                           
                         

open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovGaussianKernel RiemannGaussian.VinogradovIntervalResonance
open RiemannGaussian.VinogradovResonanceScaling RiemannGaussian.VinogradovResonanceWindow RiemannGaussian.VinogradovResonancePower
open RiemannGaussian.VinogradovRectangleResonance RiemannGaussian.VinogradovPhaseRectangle
                                                            
                        
                                       
                                                         
                                                             
                        
                                        
                                                                      
                                                           
                                                                        
                                                                                 
                      
                                                  
            
                                             
                                                                                       
                                                                                       
                     
                  
                                                                                       

end
end RiemannGaussian.VinogradovGaussianCost

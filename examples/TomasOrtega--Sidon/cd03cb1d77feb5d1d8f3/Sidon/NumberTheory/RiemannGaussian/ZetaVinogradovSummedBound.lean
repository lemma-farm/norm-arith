module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicBudget
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicDecay
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicSummation
public import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
public import Sidon.NumberTheory.RiemannGaussian.VinogradovSharperBudget
public import Sidon.NumberTheory.RiemannGaussian.ZetaDyadicTruncation
public import Sidon.NumberTheory.RiemannGaussian.ZetaEulerLineBound
public import Sidon.NumberTheory.RiemannGaussian.ZetaEulerTruncation
public import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLineBudget

@[expose] public section

namespace RiemannGaussian.ZetaVinogradovSummedBound
noncomputable section
open RiemannGaussian.DirichletDyadicBlocks RiemannGaussian.ZetaDyadicTruncation RiemannGaussian.VinogradovScaleSelection
open RiemannGaussian.VinogradovCubicBudget (growth growth_pos)
open RiemannGaussian.VinogradovSharperBudget (delta line line_bounds)
open scoped ComplexConjugate

                                                                       
                                                
                                      
                                                
                                                                     
                              
                                                             
                                                                   
          

theorem norm_le_prefix_add_six {s : ℂ} (hσ : 0 < s.re)
    (ht : 2 ≤ s.im) :
    ‖riemannZeta s‖ ≤ ‖positivePrefix s (2 ^ (depth s + 1))‖ + 6 := by
  by_cases hs : s.re ≤ 1
  · exact ZetaEulerLineBound.norm_le_prefix_add_six hσ hs ht
  · let M : ℕ := 2 ^ (depth s + 1)
    have hM : 2 ≤ M := by dsimp only [M]; rw [pow_succ]; nlinarith [Nat.one_le_pow (depth s) 2 (by omega)]
    have hMN : M - 1 + 1 = M := Nat.sub_add_cancel (by omega)
    have hcast : ((M - 1 : ℕ) : ℝ) + 1 = M := by exact_mod_cast hMN
    have hN : (0 : ℝ) < (M - 1 : ℕ) := by exact_mod_cast (show 0 < M - 1 by omega)
    have hnorm : ‖s‖ ≤ 2 * ((M - 1 : ℕ) : ℝ) := by
      have h := ZetaEulerLineBound.norm_lt_endpoint s
      change ‖s‖ < (M : ℝ) at h
      have hN1 : (1 : ℝ) ≤ (M - 1 : ℕ) := by exact_mod_cast (show 1 ≤ M - 1 by omega)
      linarith
    have hne : s ≠ 1 := by intro he; norm_num [he] at ht
    have h := ZetaEulerTruncation.norm_zeta_sub_partialSum_le hσ hne (show 1 ≤ M - 1 by omega)
    rw [ZetaEulerLineBound.partialSum_eq_positivePrefix, hMN] at h
    have hp : ((M - 1 : ℕ) : ℝ) ^ (-s.re) ≤ ((M - 1 : ℕ) : ℝ)⁻¹ := by
      have hh := Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ (M - 1 : ℕ) by exact_mod_cast (show 1 ≤ M - 1 by omega))
        (show -s.re ≤ (-1 : ℝ) by linarith)
      simpa only [Real.rpow_neg_one] using hh
    have hr : ‖s‖ / s.re * ((M - 1 : ℕ) : ℝ) ^ (-s.re) ≤ 2 := by
      calc
        _ ≤ ‖s‖ * ((M - 1 : ℕ) : ℝ)⁻¹ :=
          mul_le_mul (div_le_self (norm_nonneg s) (by linarith)) hp (by positivity) (norm_nonneg s)
        _ ≤ (2 * ((M - 1 : ℕ) : ℝ)) * ((M - 1 : ℕ) : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hnorm (by positivity)
        _ = 2 := by field_simp
    have hd : s.im ≤ ‖s - 1‖ := by
      simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.im_le_norm (s - 1)
    have he : (((M - 1 : ℕ) : ℝ) + 1) ^ (1 - s.re) / ‖s - 1‖ ≤ 1 := by
      have hp' := Real.rpow_le_one_of_one_le_of_nonpos
        (show (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) + 1 by linarith)
        (show 1 - s.re ≤ 0 by linarith)
      exact (div_le_self (by positivity) (by linarith : 1 ≤ ‖s - 1‖)).trans hp'
    have htri := norm_add_le (riemannZeta s - positivePrefix s M) (positivePrefix s M)
    simp only [sub_add_cancel] at htri
    change ‖riemannZeta s‖ ≤ ‖positivePrefix s M‖ + 6
    linarith

                                                  
                                                
                                                 
                                            
                                                                    
                                                                   
                                                                        
                                                                                        
                                    
                                    
                                                       
                                     
                                                                                  
                                                     
                                                               
              
                
                                 
                                                                   
                     
      
                                                                        
                                         
                                          
                                                                               
                             
                
                                                                 
                                                                                     
                                                       
                                                                                 
                                 
                                                  
                                                                               
                         
                                                                           
                                                                                        
                    

                                                 
                                                
                                                 
                                                                                     
                                                                   
                                                                        
                                                                                        
                                                       
                                                               
                                           
                                                                                   
                                         
                                                                                   
                                 
                                                       
                                                                                                     
                                                            
                                                                       
                                                                       
                                       
                      
           

                                                     
                                                
                                                   
                                                                                         
                        
                                 
                                       
                                                                    
                                                                             
                                                 

end
end RiemannGaussian.ZetaVinogradovSummedBound

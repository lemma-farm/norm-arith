-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Bounds for the spatial multiplier heat kernel

The multiplier clauses of equation `eq:heat-kernel-bounds` in the proof of
Proposition `prop:heat-morrey-hoelder` are the pointwise bounds for a smooth,
degree-one homogeneous spatial Fourier symbol applied to the forward heat
kernel.  The paper passage is `paper/ckn.tex`, label `eq:heat-kernel-bounds`.
-/

open scoped BigOperators
open Set MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat

private theorem integrable_frequency_gaussian_half {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : Vec3 => Real.exp (-(t / 2 * vec3EuclideanNorm ξ ^ 2))) volume := by
  have ht' : (0 : ℝ) < 1 / (2 * t) := by positivity
  have hHK := heatKernel_integrable (t := 1 / (2 * t)) ht'
  have hc : ((4 * Real.pi * (1 / (2 * t))) ^ (-(3 : ℝ) / 2)) ≠ 0 := by
    have hpos : (0 : ℝ) < 4 * Real.pi * (1 / (2 * t)) := by positivity
    positivity
  have hform : (fun ξ : Vec3 => Real.exp (-(t / 2 * vec3EuclideanNorm ξ ^ 2))) =
      fun ξ : Vec3 => ((4 * Real.pi * (1 / (2 * t))) ^ (-(3 : ℝ) / 2))⁻¹ *
        heatKernel ξ (1 / (2 * t)) := by
    funext ξ
    rw [heatKernel_eq_formula_sum ht', ← mul_assoc, inv_mul_cancel₀ hc, one_mul,
      vec3EuclideanNorm_sq]
    congr 1
    field_simp
    ring
  rw [hform]
  exact hHK.const_mul _

                                                             
                                     
                                                 
                        
                                             
                                   
                                   
                     
                                          
                     
                                                                                    
                                                                           
                       
           
             
        
      
                                     
                                                           
                   
                   
                    
                                     
                                                                       
          
                                                       
                                                                      
                                               
                                                           
                                              
                                                   
             

                                                             
                                 
                                                     
                                                                       
                                                                      
                                                             
      
                                                                          
                                                        
                                                                            
                                                                              
                                               
                                                            

                                                                         
                                     
                                                               
                                                                        
                                                                         
                                              
                           
                                                           
                                     
                                                                            
                 
                                                               
                                           
                                                                     
                       
           
        
      
                                     
                                               
                                                 
                                                  
                                                                               
                                 
                     
                  
                      
                
                                                       
                                                                   
                                             
                                                                              
                                                                 
               
                
          

private theorem measurable_frequency_gaussian_moment (t : ℝ) (n : ℕ) :
    Measurable (fun ξ : Vec3 => vec3EuclideanNorm ξ ^ n *
      Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) := by
  apply Measurable.mul
  · exact (continuous_vec3EuclideanNorm.pow n).measurable
  · apply Measurable.exp
    exact (measurable_const.mul (continuous_vec3EuclideanNorm.pow 2).measurable).neg

                                                                           
                           
                                                      
                                                               
         
             
                                                             
                                                                                                 
                         
                                                          
                                                        
                                                                                   
                                                                                     
                           
                                                                              
                                                                        
                         
                                                                
                                                                                     
                                   
                           
                                                                          
                                                                        
                         
                                                                         
                                                                                           
                                   
                           
                                                                 
                              
                                                                        
                         
                                                                 
                                                                                           
                                   

                                                                           
theorem power_mul_exp_bound {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (n : ℕ) :
    r ^ n * Real.exp (-(a * r ^ 2)) ≤
      (1 + (2 / a) ^ n * (n : ℝ) ^ n) * Real.exp (-(a / 2 * r ^ 2)) := by
  by_cases hn : n = 0
  · subst n
    have hexp : Real.exp (-(a * r ^ 2)) ≤ Real.exp (-(a / 2 * r ^ 2)) :=
      Real.exp_le_exp.mpr (by nlinarith only [ha, sq_nonneg r])
    calc
      r ^ 0 * Real.exp (-(a * r ^ 2)) = Real.exp (-(a * r ^ 2)) := by simp
      _ ≤ Real.exp (-(a / 2 * r ^ 2)) := hexp
      _ ≤ (1 + 1) * Real.exp (-(a / 2 * r ^ 2)) := by
        calc
          _ = 1 * Real.exp (-(a / 2 * r ^ 2)) := by ring
          _ ≤ (1 + 1) * Real.exp (-(a / 2 * r ^ 2)) :=
            mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_nonneg _)
      _ = (1 + (2 / a) ^ 0 * (0 : ℝ) ^ 0) *
          Real.exp (-(a / 2 * r ^ 2)) := by norm_num
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  let u : ℝ := a / 2 * r ^ 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huExp : u ^ n ≤ (n : ℝ) ^ n * Real.exp u := by
    have hdiv : u / (n : ℝ) ≤ Real.exp (u / (n : ℝ)) := by
      have h := Real.add_one_le_exp (u / (n : ℝ))
      linarith only [h]
    have hmul : u ≤ (n : ℝ) * Real.exp (u / (n : ℝ)) := by
      apply (div_le_iff₀ hnpos).mp at hdiv
      nlinarith only [hdiv]
    calc
      u ^ n ≤ ((n : ℝ) * Real.exp (u / (n : ℝ))) ^ n :=
        pow_le_pow_left₀ hu hmul n
      _ = (n : ℝ) ^ n * Real.exp u := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 1
        dsimp [u]
        field_simp
  have hpow : r ^ n ≤ 1 + r ^ (2 * n) := by
    by_cases hr1 : r ≤ 1
    · have hp : r ^ n ≤ 1 := pow_le_one₀ hr hr1
      exact hp.trans (le_add_of_nonneg_right (pow_nonneg hr _))
    · have hr1' : 1 ≤ r := le_of_not_ge hr1
      have hp : r ^ n ≤ r ^ (2 * n) :=
        pow_le_pow_right₀ hr1' (by omega)
      linarith only [hp]
  have htwo : r ^ (2 * n) = (2 / a) ^ n * u ^ n := by
    calc
      r ^ (2 * n) = (r ^ 2) ^ n := by rw [pow_mul]
      _ = ((2 / a) * (a / 2 * r ^ 2)) ^ n := by
        congr 1
        field_simp
      _ = (2 / a) ^ n * u ^ n := by rw [mul_pow]
  have hexp : Real.exp (-(a * r ^ 2)) =
      Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  have hbase : Real.exp (-(a * r ^ 2)) ≤ Real.exp (-(a / 2 * r ^ 2)) :=
    Real.exp_le_exp.mpr (by nlinarith only [ha, sq_nonneg r])
  have hhigh : r ^ (2 * n) * Real.exp (-(a * r ^ 2)) ≤
      ((2 / a) ^ n * (n : ℝ) ^ n) *
        Real.exp (-(a / 2 * r ^ 2)) := by
    rw [htwo, hexp]
    have hmul := mul_le_mul_of_nonneg_left huExp (pow_nonneg (by positivity : 0 ≤ 2 / a) n)
    have hprod : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      (2 / a) ^ n * u ^ n * (Real.exp (-u) * Real.exp (-u)) ≤
          (2 / a) ^ n * ((n : ℝ) ^ n * Real.exp u) *
            (Real.exp (-u) * Real.exp (-u)) := by
              apply mul_le_mul_of_nonneg_right hmul
              exact mul_nonneg (Real.exp_nonneg (-u)) (Real.exp_nonneg (-u))
      _ = ((2 / a) ^ n * (n : ℝ) ^ n) * Real.exp (-u) := by
        calc
          _ = ((2 / a) ^ n * (n : ℝ) ^ n) *
              (Real.exp u * Real.exp (-u)) * Real.exp (-u) := by ring
          _ = ((2 / a) ^ n * (n : ℝ) ^ n) * Real.exp (-u) := by rw [hprod]; ring
      _ = ((2 / a) ^ n * (n : ℝ) ^ n) *
          Real.exp (-(a / 2 * r ^ 2)) := by congr 2
  calc
    r ^ n * Real.exp (-(a * r ^ 2)) ≤
        (1 + r ^ (2 * n)) * Real.exp (-(a * r ^ 2)) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = Real.exp (-(a * r ^ 2)) +
        r ^ (2 * n) * Real.exp (-(a * r ^ 2)) := by ring
    _ ≤ Real.exp (-(a / 2 * r ^ 2)) +
        ((2 / a) ^ n * (n : ℝ) ^ n) *
          Real.exp (-(a / 2 * r ^ 2)) := add_le_add hbase hhigh
    _ = (1 + (2 / a) ^ n * (n : ℝ) ^ n) *
        Real.exp (-(a / 2 * r ^ 2)) := by ring

/-- Every polynomial moment of a positive Gaussian is integrable in frequency space. -/
theorem integrable_frequency_gaussian_moment_all {t : ℝ} (ht : 0 < t)
    (n : ℕ) : Integrable (fun ξ : Vec3 => vec3EuclideanNorm ξ ^ n *
      Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) volume := by
  refine Integrable.mono'
    ((integrable_frequency_gaussian_half (t := t) ht).const_mul
      (1 + (2 / t) ^ n * (n : ℝ) ^ n))
    (measurable_frequency_gaussian_moment t n).aestronglyMeasurable ?_
  filter_upwards with ξ
  simpa only [Real.norm_of_nonneg (mul_nonneg
    (pow_nonneg (vec3EuclideanNorm_nonneg ξ) _) (Real.exp_nonneg _))] using
    power_mul_exp_bound ht (vec3EuclideanNorm_nonneg ξ) n

/-- The continuous linear functional pairing a frequency with a spatial point. -/
def frequencyPairingCLM (ξ : Vec3) : Vec3 →L[ℝ] ℝ :=
  ∑ j : Fin 3, (ξ j) • ContinuousLinearMap.proj j

/-- Evaluation of the coordinate pairing. -/
theorem frequencyPairingCLM_apply (ξ x : Vec3) :
    frequencyPairingCLM ξ x = ∑ j : Fin 3, ξ j * x j := by
  simp [frequencyPairingCLM]

/-- An operator-norm estimate for the coordinate pairing. -/
theorem frequencyPairingCLM_norm_le (ξ : Vec3) :
    ‖frequencyPairingCLM ξ‖ ≤ 3 * vec3EuclideanNorm ξ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by norm_num) (vec3EuclideanNorm_nonneg ξ)) fun x => ?_
  rw [frequencyPairingCLM_apply, Real.norm_eq_abs]
  calc
    |∑ j : Fin 3, ξ j * x j| ≤ ∑ j : Fin 3, |ξ j * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin 3, |ξ j| * |x j| := by simp [abs_mul]
    _ ≤ ∑ _j : Fin 3, vec3EuclideanNorm ξ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul (abs_apply_le_vec3EuclideanNorm ξ j)
        (norm_le_pi_norm x j) (abs_nonneg (x j)) (vec3EuclideanNorm_nonneg ξ)
    _ = 3 * vec3EuclideanNorm ξ * ‖x‖ := by
      simp [Finset.sum_const, Fintype.card_fin]
      ring

private def frequencyArgumentCLM (ξ : Vec3) : Vec3 →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp
    (Complex.ofRealCLM.comp (frequencyPairingCLM ξ))

private theorem frequencyArgumentCLM_apply (ξ x : Vec3) :
    frequencyArgumentCLM ξ x = Complex.I *
      ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ) := by
  have hsum : (∑ j : Fin 3, ξ j * x j : ℝ) = ∑ j : Fin 3, x j * ξ j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp [frequencyArgumentCLM, frequencyPairingCLM_apply, hsum]
  rw [← Finset.mul_sum]

private def frequencyPhase (ξ : Vec3) : Vec3 → ℂ :=
  fun x => NormedSpace.exp (frequencyArgumentCLM ξ x)

                                                         
                                  
                                                                          
                                         
                                                   
                                                              
                                          
                       
       
         
        

private theorem spatialMultiplierHeatIntegrand_eq_frequencyPhase
    (σ : Vec3 → ℂ) (x : Vec3) (t : ℝ) (ξ : Vec3) :
    spatialMultiplierHeatIntegrand σ x t ξ =
      frequencyPhase ξ x * σ ξ *
        Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) := by
  unfold spatialMultiplierHeatIntegrand
  rw [frequencyPhase, ← Complex.exp_eq_exp_ℂ, frequencyArgumentCLM_apply]

                                                         
                                                            
                                                               
                                                             
           
                                    
                 
        
                                                      
                                                           
      
                              
                                                   
                                                             
                                            
                                                                 
          
                                                                   
                                                       
                                                                  
                                                           
                                                                       
                                                                

private theorem frequencyPhase_norm (ξ x : Vec3) : ‖frequencyPhase ξ x‖ = 1 := by
  rw [frequencyPhase, ← Complex.exp_eq_exp_ℂ, frequencyArgumentCLM_apply, Complex.norm_exp]
  simp

                                                           
                                                                    
                                                               
                
                                                                          
                                                             
           
                                                                 
                 
                                                                   
                               
                                   
              
      
                                                                    
                                   
                                                                    
                                                                            
                                           
                                                               
                                       
                                          

theorem norm_spatialMultiplierHeatIntegrand
    (σ : Vec3 → ℂ) (x : Vec3) (t : ℝ) (ξ : Vec3) :
    ‖spatialMultiplierHeatIntegrand σ x t ξ‖ =
      ‖σ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
  have hgauss : ‖Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))‖ =
      Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
    rw [Complex.norm_exp]
    have hre : (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)).re =
        -(t * vec3EuclideanNorm ξ ^ 2) := by
      rw [Complex.neg_re, Complex.ofReal_re]
    rw [hre]
  rw [spatialMultiplierHeatIntegrand_eq_frequencyPhase]
  calc
    ‖frequencyPhase ξ x * σ ξ *
        Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))‖ =
        ‖frequencyPhase ξ x‖ * ‖σ ξ‖ *
          ‖Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))‖ := by simp
    _ = ‖σ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
      rw [frequencyPhase_norm, hgauss]
      ring

                                                                        
                                                             
                                                                     
                 
                                                                        
                                           
                                                                    
                                                                         
                                                                             
                         
                                                                               
                                                               
                       
                                       
                                                   
                                                          
                                                                    
                                                                     
                       
      
                                                               
                                                                              
                                   
                                                              
                                                                               
                                   
                                                                            
                               
                                                                         
                                                                               
                                      
                                      
                                                             

                                                                        
                                                             
                                                                       
                                                                        
                                                          
                                                                    
                                                                         
                                       
                                              
                                                                             
                         
                                                                               
                                                               
                       
                                       
                                                            
                                                        
                                   
                                                                                   
             
                                                                     
                       
      
                                                                                 
                                   
                                                                                     
          
                                                                                     
                                                                
                                                 
                                       
                                                                                    
                                           
                                                  
                                      
                                                             

end CKN.Foundation.Euclidean

/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import QuadraticCarleson.FiniteModulationKernelComparison
                                         
import QuadraticCarleson.DyadicKernelInfinite
import QuadraticCarleson.KrauseLaceyFiniteRadiusAdapter
import QuadraticCarleson.KrauseLaceyThreeShiftAction

/-!
# From sharp truncations to the smooth Krause--Lacey pieces

The Krause--Lacey stopping argument is naturally formulated for smooth dyadic
pieces, whereas the paper ultimately needs a maximum of sharp truncations.
This file proves the deterministic part of that passage.

Every positive radius is rounded upward to a dyadic radius lying between
`ε` and `2ε`.  The resulting annular error is bounded by eight copies of the
centered Hardy--Littlewood maximal function.  At the rounded radius, the
sharp tail is then decomposed exactly into a smooth high-pass cutoff and the
already-controlled cutoff boundary error.  Thus the complete loss in the
two deterministic replacements is sixteen copies of the maximal function.

What is *not* asserted here is the analytic Krause--Lacey sparse estimate for
the smooth high-pass maximum.  That is precisely the remaining oscillatory
input, rather than an assumption hidden in this adapter.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceySharpSmoothAdapter

open KrauseLaceyFiniteRadiusAdapter
open QuadraticHilbertMaximalMeasurable

set_option autoImplicit false

noncomputable section

                                                                      
                                                
                                                         

                                                   
                                                
                                       

                                                      
                                         
                                                     
                                                                   

                                                   
                                
                          

                                                  
                                
                                  

                                                          
                                       
                                                                  
                                               

                                                                           
                                      
                                                                          
                           
                                                       
                                            
                                          
                          

                                                                       
def radiusRoundingBoundaryKernel (lam ε ρ t : ℝ) : ℂ :=
  sharpQuadraticTailKernel lam ε t - sharpQuadraticTailKernel lam ρ t

                                                               
                                                        
                                                 
                                               

theorem radiusRoundingBoundaryKernel_eq_zero_of_abs_le
    (lam : ℝ) {ε ρ t : ℝ} (hερ : ε ≤ ρ) (ht : |t| ≤ ε) :
    radiusRoundingBoundaryKernel lam ε ρ t = 0 := by
  simp [radiusRoundingBoundaryKernel, sharpQuadraticTailKernel,
    not_lt.mpr ht, not_lt.mpr (ht.trans hερ)]

theorem radiusRoundingBoundaryKernel_eq_zero_of_rho_lt_abs
    (lam : ℝ) {ε ρ t : ℝ} (hερ : ε ≤ ρ) (ht : ρ < |t|) :
    radiusRoundingBoundaryKernel lam ε ρ t = 0 := by
  have hεt : ε < |t| := lt_of_le_of_lt hερ ht
  simp [radiusRoundingBoundaryKernel, sharpQuadraticTailKernel, hεt, ht]

theorem radiusRoundingBoundaryKernel_norm_le
    (lam : ℝ) {ε ρ t : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) :
    ‖radiusRoundingBoundaryKernel lam ε ρ t‖ ≤ 1 / ε := by
  by_cases hεt : ε < |t|
  · by_cases hρt : ρ < |t|
    · simp [radiusRoundingBoundaryKernel, sharpQuadraticTailKernel, hεt, hρt,
        hε.le]
    · simp only [radiusRoundingBoundaryKernel, sharpQuadraticTailKernel,
        if_pos hεt, if_neg hρt, sub_zero, norm_div, norm_phase,
        Complex.norm_real, Real.norm_eq_abs]
      exact one_div_le_one_div_of_le hε hεt.le
  · have htε : |t| ≤ ε := le_of_not_gt hεt
    rw [radiusRoundingBoundaryKernel_eq_zero_of_abs_le lam hερ htε]
    simpa using one_div_nonneg.mpr hε.le

theorem radiusRoundingBoundaryKernel_support_subset
    (lam : ℝ) {ε ρ : ℝ} (hερ : ε ≤ ρ) :
    support (radiusRoundingBoundaryKernel lam ε ρ) ⊆ closedBall 0 ρ := by
  intro t ht
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  by_contra h
  exact ht (radiusRoundingBoundaryKernel_eq_zero_of_rho_lt_abs lam hερ (lt_of_not_ge h))

private theorem integrable_kernel_mul
    {f : ℝ → ℂ} (hfi : Integrable f) (x : ℝ) {k : ℝ → ℂ} {C : ℝ}
    (hk : Measurable k) (hbound : ∀ t, ‖k t‖ ≤ C) :
    Integrable (fun y ↦ k (x - y) * f y) := by
  apply hfi.bdd_mul
  · exact (hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun y ↦ hbound (x - y))

/-- Exact operator identity for upward radius rounding. -/
theorem quadraticHilbertTrunc_sub_rounded_eq_boundary
    (lam : ℝ) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    {f : ℝ → ℂ} (hfi : Integrable f) (x : ℝ) :
    quadraticHilbertTrunc lam ε f x - quadraticHilbertTrunc lam ρ f x =
      ∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y := by
  have hεi : Integrable
      (fun y ↦ sharpQuadraticTailKernel lam ε (x - y) * f y) :=
    integrable_kernel_mul hfi x (measurable_sharpQuadraticTailKernel lam ε)
      (fun t ↦ sharpQuadraticTailKernel_norm_le lam (t := t) hε)
  have hρi : Integrable
      (fun y ↦ sharpQuadraticTailKernel lam ρ (x - y) * f y) :=
    integrable_kernel_mul hfi x (measurable_sharpQuadraticTailKernel lam ρ)
      (fun t ↦ sharpQuadraticTailKernel_norm_le lam (t := t) hρ)
  rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc,
    ← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc,
    quadraticHilbertConvolutionTrunc, quadraticHilbertConvolutionTrunc,
    ← integral_sub hεi hρi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    simp only [Pi.sub_apply, radiusRoundingBoundaryKernel, sub_mul])

/-- Rounding a truncation radius upward by at most a factor two costs at
most eight copies of the centered Hardy--Littlewood maximal function. -/
theorem radiusRoundingBoundaryOperator_enorm_le_maximal
    (lam : ℝ) {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) (hρε : ρ ≤ 2 * ε)
    (f : ℝ → ℂ) (hf : Measurable f) (x : ℝ) :
    ‖∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ ≤
      8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  have hρ : 0 < ρ := hε.trans_le hερ
  calc
    ‖∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ ≤
        ∫⁻ y, ‖radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in closedBall x (2 * ε),
          ENNReal.ofReal (1 / ε) * ‖f y‖ₑ := by
      rw [← lintegral_indicator measurableSet_closedBall]
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ closedBall x (2 * ε)
      · simp only [indicator_of_mem hy, enorm_mul]
        apply mul_le_mul'
        · simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal
            (radiusRoundingBoundaryKernel_norm_le lam hε hερ)
        · exact le_rfl
      · simp only [indicator, hy, ↓reduceIte]
        have hk : radiusRoundingBoundaryKernel lam ε ρ (x - y) = 0 := by
          apply notMem_support.mp
          intro hmem
          apply hy
          have hs := radiusRoundingBoundaryKernel_support_subset lam hερ hmem
          have hxyρ : |x - y| ≤ ρ := by
            simpa [mem_closedBall, Real.dist_eq, abs_sub_comm] using hs
          simpa [mem_closedBall, Real.dist_eq, abs_sub_comm] using hxyρ.trans hρε
        simp [hk]
    _ = 4 * centeredAverage (2 * ε) (fun y ↦ ‖f y‖ₑ) x := by
      rw [MeasureTheory.lintegral_const_mul _ hf.enorm]
      unfold centeredAverage
      have hε0 : ε ≠ 0 := ne_of_gt hε
      rw [show ENNReal.ofReal (1 / ε) =
          4 / ENNReal.ofReal (2 * (2 * ε)) by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp
        <;> ring]
      simp only [ENNReal.div_eq_inv_mul]
      ac_rfl
    _ ≤ 8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
      have h := centeredAverage_le_two_mul_centeredHardyLittlewoodMaximal
        (mul_pos (by norm_num : (0 : ℝ) < 2) hε) (fun y ↦ ‖f y‖ₑ) x
      calc
        4 * centeredAverage (2 * ε) (fun y ↦ ‖f y‖ₑ) x ≤
            4 * (2 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) :=
          mul_le_mul' le_rfl h
        _ = _ := by rw [← mul_assoc]; norm_num

                                                           
                                                                
                                              
                                                      
                                        
                                                                
                                                                   
                                
                                              
                                                   
                                                          
                                                                           
                                                                                  
      
                                        
                                          
                                                                         
             
                            
                                            
                                                                       
                      
                                 

                                                                          
                                                                       
def smoothQuadraticHighPassKernel (lam ρ t : ℝ) : ℂ :=
  if t = 0 then 0 else
    ((((1 - dyadicCutoff (t / (4 * ρ))) / t : ℝ) : ℂ) *
      phase (lam * t ^ 2))

                                                        
                                                               
                                            
               
                           
                                                     
                                     
                                            
            
         
      

                                                                           
                                                                    
                                                    
                                        
                                                     
                               
                                                             
                                                                           
                     
           
                                                        
                                            
                    
                                                     
                                                                       
                                  
                                                 
                   
                                                 
                                     

                                                                
                                                     
                                            
                                                                 
               
                                                                 
                                   
                                                  
                                                     
                                     

                                            
                               
                       
                                                              
                                                                     
                                                    
                                     
                                                         

                                                                      
                              
theorem sharpQuadraticTailKernel_eq_smoothHighPass_add_boundary
    (lam ρ t : ℝ) :
    sharpQuadraticTailKernel lam ρ t =
      smoothQuadraticHighPassKernel lam ρ t + cutoffBoundaryKernel lam ρ t := by
  by_cases ht0 : t = 0
  · simp [ht0, sharpQuadraticTailKernel, smoothQuadraticHighPassKernel,
      cutoffBoundaryKernel]
  · rw [smoothQuadraticHighPassKernel, cutoffBoundaryKernel, if_neg ht0, if_neg ht0]
    by_cases ht : ρ < |t|
    · have hnot : ¬ |t| ≤ ρ := not_le.mpr ht
      rw [sharpQuadraticTailKernel, if_pos ht, if_neg hnot]
      push_cast
      field_simp
      <;> ring
    · have hle : |t| ≤ ρ := le_of_not_gt ht
      rw [sharpQuadraticTailKernel, if_neg ht, if_pos hle]
      push_cast
      field_simp
      <;> ring

/-- Smooth high-pass convolution operator. -/
def smoothQuadraticHighPass
    (lam ρ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, smoothQuadraticHighPassKernel lam ρ (x - y) * f y

                                                                    
                                                                     
                                             

theorem measurable_smoothQuadraticHighPassKernel (lam ρ : ℝ) :
    Measurable (smoothQuadraticHighPassKernel lam ρ) := by
  have hnum : Measurable (fun t : ℝ ↦ 1 - dyadicCutoff (t / (4 * ρ))) :=
    measurable_const.sub (dyadicCutoff_smooth.continuous.measurable.comp
      (measurable_id.div_const (4 * ρ)))
  have hp : Measurable (fun t : ℝ ↦ phase (lam * t ^ 2)) := by
    unfold phase
    fun_prop
  apply Measurable.ite (measurableSet_singleton 0)
  · exact measurable_const
  · exact (Complex.measurable_ofReal.comp (hnum.div measurable_id)).mul hp

theorem smoothQuadraticHighPassKernel_norm_le
    (lam : ℝ) {ρ t : ℝ} (hρ : 0 < ρ) :
    ‖smoothQuadraticHighPassKernel lam ρ t‖ ≤ 2 / ρ := by
  have hs := sharpQuadraticTailKernel_norm_le lam (t := t) hρ
  have hb := cutoffBoundaryKernel_norm_le lam (t := t) hρ
  have heq := sharpQuadraticTailKernel_eq_smoothHighPass_add_boundary lam ρ t
  have heq' : smoothQuadraticHighPassKernel lam ρ t =
      sharpQuadraticTailKernel lam ρ t - cutoffBoundaryKernel lam ρ t := by
    exact eq_sub_iff_add_eq.mpr heq.symm
  calc
    ‖smoothQuadraticHighPassKernel lam ρ t‖ =
        ‖sharpQuadraticTailKernel lam ρ t - cutoffBoundaryKernel lam ρ t‖ := by rw [heq']
    _ ≤
        ‖sharpQuadraticTailKernel lam ρ t‖ +
          ‖cutoffBoundaryKernel lam ρ t‖ := norm_sub_le _ _
    _ ≤ 1 / ρ + 1 / ρ := add_le_add hs hb
    _ = 2 / ρ := by ring

                                   
                                                               
                                                          
                                                                                 
                      
                                                                    
                                        
                                                      
                                                                     
                      
                                                                    
                                        
                                                      
                                                                     
                                                       
                                                  
                         
                                               
                                                                        
         

                                    
                                                                      
                                                           
                                                 
                                                                             
                         
                                               
                                                                    
                                                             
         

                                                       
                                    
                                                                 
             
               
                                                                                
                         
               
                                                                                 
               
       

                                           
                               
                                                 
                                 
                                 
           
                                                        
              
                         
              
             
                                 
                                            
                                                         
        
                                                         
                                     
                                                                                
                 

                                                            
                           
                                                      
                                                              
                
            
                                                                                          

                                                    
                                                
                                      
                                              
                                                  
                                                                             
                      
                                                
              
                           
                                                                     
                                                    
                                                                          
                                                   
                                                             
                       
                                               
                                     
                                         
            
                                                         
                                                          
                                                                             
                
              
                       
             
                                                    
                                                                
             

                                                                           
                                                                         
                                                                     
                                                  
                                                
                            
                                                
                                           
                                                                 
                              
                                            
                                      
                                          
                                              
                                                          
                                                               
                                                                          
                                                             
                                                       
              
                                                
               
            
                                                         
             
                                                         
                                     
                                           
                                                                            
                                                                                  
                        
          

                                                                            
                                                                           
                                                                      
                                                                          
                      
                                                                    
                                      
                                
                       
                                                        
                                                         
                                    
                                                                   
                                                       
                  
                                
                                                                        
                             
                   
                                                                                   
                         
                        
                                                                            
                                            
                                     
                                       
                   
                                                           
                      
                                                                 
                                                     
         
      
                              
                        
                                                              
                                     
                                                                       
                           
                 
                                                             
                                                                     
                               
                                
                        
                                     
                                  
                                                                        
                             
                                     
                                
                        
                                                       
                                                          
                                                           
                                                         
             
                   
                                                               
                                 
                   
            
                                                 
                                               
             
                           

                                                        
theorem quadraticHilbertTrunc_eq_smoothHighPass_add_boundary
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {f : ℝ → ℂ}
    (hfi : Integrable f) (x : ℝ) :
    quadraticHilbertTrunc lam ρ f x = smoothQuadraticHighPass lam ρ f x +
      ∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y := by
  have hsmooth : Integrable
      (fun y ↦ smoothQuadraticHighPassKernel lam ρ (x - y) * f y) :=
    integrable_kernel_mul hfi x (measurable_smoothQuadraticHighPassKernel lam ρ)
      (fun t ↦ smoothQuadraticHighPassKernel_norm_le lam (t := t) hρ)
  have hboundary : Integrable
      (fun y ↦ cutoffBoundaryKernel lam ρ (x - y) * f y) :=
    integrable_kernel_mul hfi x (measurable_cutoffBoundaryKernel lam ρ)
      (fun t ↦ cutoffBoundaryKernel_norm_le lam (t := t) hρ)
  rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc,
    quadraticHilbertConvolutionTrunc, smoothQuadraticHighPass, ← integral_add hsmooth hboundary]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    dsimp only
    rw [← add_mul, ← sharpQuadraticTailKernel_eq_smoothHighPass_add_boundary])

                                                                          
                                                               
                                                                 
                                              
                                                      
                                        
                                            
                                                                   
                                                                      
                                                   
                                                            

                                                                        
                                                                    
                                                                       
                                              
                                                      
                                        
                                                                  
                                                                    
                                                                         
                   
                                                                           
                                            
      
                                        
                                                                  
                                                                         
                                                                     
                                                                  
                                                                  
                               
                    

                                                                        
                                                 
                                       
                                             
                                        
               
                                
                                          

                                                                         
                                                                      
                                             
                                                               
                                                                     

                                                              
                                                                        
                                                           
                                                         
                                                                   
                                    
                           

                                                                         
                                 
                                                             
                                                             
                                                                  
                      
                                                               
                                        
                                                 
                                                                
                                                                  
                                     
      
                                                         
                                                              
                                      
                                  
                                                                       
             
                
                   
                                      
                                                                              
                                                      

                                     
                                                                       
                                      
                                                                     
                                                                
                                                                                        
           
                                          
                                                                  
                                                
                                              
                   
                          
                                                                 
                                                                                         
                         
                                                                 
                                                  
                            
            
                                                
                                               
                                         
                                               
                                                         
                                                                            
                                                                        
                                                             
                         
                 
                                
                                            
                                                      
        
                                                                     
                                                              
                   
                                                                           
                                                                   
                                    
                                   
                                          
                                                 
                               
                   
                                                                   
                        

                                                  
                                                                          
                                                                      
                                                     
                                                           
           
                                            
                     
            
      
                                                               
                                  
                                                                         
                                                                                
                                                                             
                                                                           
                                                                            
                       
                                                   
                                                 
                                                  
                                                 
                                                      
                                                                              
                                             
                                                                                

                                                
                                                     
                              
                                                                       
                                                                
           
                                            
      
                                               
                                                                   
                                                      
                                                    
                                
               
                                          
                                           
                                                         
                                                    
             
              
                     
                                                          
                                                  
                                           

                                                             
                                               
                                                                       
             
               
                                                              
                                                                         
               
                                                              
                                                 
       

                                                                 
                                     
                                                          
                                            
                 
                                                     

                                                                         
                                                                       
                                                            
                                                                   
                                                                        
                  
                                                                 
                    
                                                                 
                                                                    
           
                                                       
                                                   
                                                         
                                                                                  
                                                   
                     
             
      
                                                      
                                                    
                            
                                    
                                                
                                                                   
                                                                     
                                                   
                      
                                        
                                                           
                                                                      
                      
                                                            
                                                      
                                                             
                    
                


end
end KrauseLaceySharpSmoothAdapter
end QuadraticCarleson

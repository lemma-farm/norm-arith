/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.PositiveDyadicKernel
import QuadraticCarleson.IntervalMaximalComparison

/-!
# The finite low-modulation block versus maximal truncations

This is the elementary pointwise reduction at the start of the proof of the
finite-modulation weak-type corollary in the accompanying article
([arXiv:2609.04101v1](https://arxiv.org/abs/2609.04101v1)). A
consecutive block of the paper's smooth dyadic kernels telescopes.  Replacing
its two smooth cutoffs by sharp cutoffs produces the difference of two
quadratic Hilbert truncations; the two transition annuli are controlled by
the centered Hardy--Littlewood maximal function.

The later sparse input in the paper is [Krause--Lacey, Theorem 1.1], namely a
uniform sparse `(1,p)` estimate for the maximally truncated quadratic Hilbert
transform.  Mathlib has no Carleson or oscillatory sparse-bound development,
and the project currently only defines the abstract sparse premise in
`FiniteSparseMaximal`.  Accordingly, this file proves the concrete pointwise
comparison without postulating that external theorem.
-/

open Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace QuadraticCarleson

set_option autoImplicit false

                                                                          
                                                                 
                                                   
                                           
                                                            

                                                            
noncomputable def sharpQuadraticTailKernel (lam ε t : ℝ) : ℂ :=
  if ε < |t| then phase (lam * t ^ 2) / (t : ℂ) else 0

/-- Convolution orientation of a sharp quadratic Hilbert truncation. -/
noncomputable def quadraticHilbertConvolutionTrunc
    (lam ε : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, sharpQuadraticTailKernel lam ε (x - y) * f y

/-- The boundary error made when the smooth cutoff at radius `ρ` is replaced
by the sharp cutoff of the centered interval of radius `ρ`. -/
noncomputable def cutoffBoundaryKernel (lam ρ t : ℝ) : ℂ :=
  if t = 0 then 0 else
    (((dyadicCutoff (t / (4 * ρ)) - if |t| ≤ ρ then 1 else 0) / t : ℝ) : ℂ) *
      phase (lam * t ^ 2)

                                                                          
                     
                                            
                                                        
                                                                     

                                                                   
                                                                     
                                                                   
                                     
                                                                              
                                     
                                                      
                                    

                                                                          
                                                            
theorem centeredAverage_le_two_mul_centeredHardyLittlewoodMaximal
    {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ≥0∞) (x : ℝ) :
    centeredAverage r g x ≤ 2 * centeredHardyLittlewoodMaximal g x := by
  obtain ⟨q0, hrq, hq2r⟩ := exists_rat_btwn (show r < 2 * r by linarith)
  let q : PositiveRational := ⟨q0, by exact_mod_cast hr.trans hrq⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property
  have hsubset : closedBall x r ⊆ closedBall x (q : ℝ) :=
    closedBall_subset_closedBall hrq.le
  have hmass : (∫⁻ y in closedBall x r, g y) ≤
      ∫⁻ y in closedBall x (q : ℝ), g y := lintegral_mono_set hsubset
  have hrden : ENNReal.ofReal (2 * r) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hqden : ENNReal.ofReal (2 * (q : ℝ)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hqtop : ENNReal.ofReal (2 * (q : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hden : ENNReal.ofReal (2 * (q : ℝ)) ≤ 2 * ENNReal.ofReal (2 * r) := by
    rw [← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  unfold centeredAverage
  calc
    (∫⁻ y in closedBall x r, g y) / ENNReal.ofReal (2 * r) ≤
        (∫⁻ y in closedBall x (q : ℝ), g y) / ENNReal.ofReal (2 * r) :=
      ENNReal.div_le_div_right hmass _
    _ ≤ 2 * ((∫⁻ y in closedBall x (q : ℝ), g y) /
          ENNReal.ofReal (2 * (q : ℝ))) := by
      apply (ENNReal.div_le_iff hrden ENNReal.ofReal_ne_top).2
      calc
        (∫⁻ y in closedBall x (q : ℝ), g y) =
            ((∫⁻ y in closedBall x (q : ℝ), g y) /
              ENNReal.ofReal (2 * (q : ℝ))) *
                ENNReal.ofReal (2 * (q : ℝ)) := by
          exact (ENNReal.div_mul_cancel hqden hqtop).symm
        _ ≤ ((∫⁻ y in closedBall x (q : ℝ), g y) /
              ENNReal.ofReal (2 * (q : ℝ))) *
                (2 * ENNReal.ofReal (2 * r)) := mul_le_mul' le_rfl hden
        _ = 2 * ((∫⁻ y in closedBall x (q : ℝ), g y) /
              ENNReal.ofReal (2 * (q : ℝ))) * ENNReal.ofReal (2 * r) := by
          ac_rfl
    _ ≤ 2 * centeredHardyLittlewoodMaximal g x := by
      exact mul_le_mul' le_rfl
        (le_iSup (fun q' : PositiveRational ↦ centeredAverage (q' : ℝ) g x) q)

theorem cutoffBoundaryKernel_eq_zero_of_abs_le
    (lam : ℝ) {ρ t : ℝ} (hρ : 0 < ρ) (ht : |t| ≤ ρ) :
    cutoffBoundaryKernel lam ρ t = 0 := by
  by_cases ht0 : t = 0
  · simp [cutoffBoundaryKernel, ht0]
  · have hden : 0 < 4 * ρ := by positivity
    have harg : |t / (4 * ρ)| ≤ 1 / 4 := by
      rw [abs_div, abs_of_pos hden]
      apply (div_le_iff₀ hden).2
      nlinarith
    rw [cutoffBoundaryKernel, if_neg ht0, if_pos ht,
      dyadicCutoff_eq_one harg]
    simp

theorem cutoffBoundaryKernel_eq_zero_of_two_mul_le_abs
    (lam : ℝ) {ρ t : ℝ} (hρ : 0 < ρ) (ht : 2 * ρ ≤ |t|) :
    cutoffBoundaryKernel lam ρ t = 0 := by
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    simp at ht
    linarith
  have hnball : ¬ |t| ≤ ρ := by linarith
  have hden : 0 < 4 * ρ := by positivity
  have harg : 1 / 2 ≤ |t / (4 * ρ)| := by
    rw [abs_div, abs_of_pos hden]
    apply (le_div_iff₀ hden).2
    nlinarith
  rw [cutoffBoundaryKernel, if_neg ht0, if_neg hnball,
    dyadicCutoff_eq_zero harg]
  simp

theorem cutoffBoundaryKernel_norm_le
    (lam : ℝ) {ρ t : ℝ} (hρ : 0 < ρ) :
    ‖cutoffBoundaryKernel lam ρ t‖ ≤ 1 / ρ := by
  by_cases hin : |t| ≤ ρ
  · rw [cutoffBoundaryKernel_eq_zero_of_abs_le lam hρ hin]
    simpa using one_div_nonneg.mpr hρ.le
  · by_cases hout : 2 * ρ ≤ |t|
    · rw [cutoffBoundaryKernel_eq_zero_of_two_mul_le_abs lam hρ hout]
      simpa using one_div_nonneg.mpr hρ.le
    · have ht0 : t ≠ 0 := by
        intro h
        apply hin
        simp [h, hρ.le]
      have hρt : ρ < |t| := lt_of_not_ge hin
      rw [cutoffBoundaryKernel, if_neg ht0, if_neg hin, norm_mul, norm_phase,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div]
      simp only [sub_zero]
      rw [abs_of_nonneg (dyadicCutoff_nonneg _)]
      calc
        dyadicCutoff (t / (4 * ρ)) / |t| ≤ 1 / |t| :=
          div_le_div_of_nonneg_right (dyadicCutoff_le_one _) (abs_nonneg _)
        _ ≤ 1 / ρ := one_div_le_one_div_of_le hρ hρt.le

theorem measurable_sharpQuadraticTailKernel (lam ε : ℝ) :
    Measurable (sharpQuadraticTailKernel lam ε) := by
  have hp : Continuous (fun t : ℝ ↦ phase (lam * t ^ 2)) := by
    unfold phase
    fun_prop
  apply Measurable.ite
  · exact measurableSet_lt measurable_const measurable_id.abs
  · exact hp.measurable.div (Complex.measurable_ofReal.comp measurable_id)
  · exact measurable_const

theorem sharpQuadraticTailKernel_norm_le
    (lam : ℝ) {ε t : ℝ} (hε : 0 < ε) :
    ‖sharpQuadraticTailKernel lam ε t‖ ≤ 1 / ε := by
  by_cases ht : ε < |t|
  · have ht0 : t ≠ 0 := by
      intro h
      subst t
      exact (not_lt_of_ge hε.le) (by simpa only [abs_zero] using ht)
    rw [sharpQuadraticTailKernel, if_pos ht, norm_div, norm_phase,
      Complex.norm_real, Real.norm_eq_abs]
    exact one_div_le_one_div_of_le hε ht.le
  · rw [sharpQuadraticTailKernel, if_neg ht]
    simpa using one_div_nonneg.mpr hε.le

theorem measurable_cutoffBoundaryKernel (lam ρ : ℝ) :
    Measurable (cutoffBoundaryKernel lam ρ) := by
  have hp : Measurable (fun t : ℝ ↦ phase (lam * t ^ 2)) := by
    unfold phase
    fun_prop
  have hnum : Measurable (fun t : ℝ ↦
      dyadicCutoff (t / (4 * ρ)) - if |t| ≤ ρ then 1 else 0) :=
    (dyadicCutoff_smooth.continuous.measurable.comp
        (measurable_id.div_const (4 * ρ))).sub
      (measurable_const.ite
        (measurableSet_le measurable_id.abs measurable_const)
        measurable_const)
  apply Measurable.ite (measurableSet_singleton 0)
  · exact measurable_const
  · apply Measurable.mul
    · exact Complex.measurable_ofReal.comp (hnum.div measurable_id)
    · exact hp

private theorem integrable_kernel_mul
    {f : ℝ → ℂ} (hfi : Integrable f) (x : ℝ) {k : ℝ → ℂ} {C : ℝ}
    (hk : Measurable k) (hbound : ∀ t, ‖k t‖ ≤ C) :
    Integrable (fun y ↦ k (x - y) * f y) := by
  apply hfi.bdd_mul
  · exact (hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun y ↦ hbound (x - y))

/-- The convolution-oriented truncation is exactly the truncation already
defined in `Definitions`. -/
theorem quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc
    (lam ε : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    quadraticHilbertConvolutionTrunc lam ε f x =
      quadraticHilbertTrunc lam ε f x := by
  let s : Set ℝ := {u : ℝ | ε < |u|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const measurable_id.abs
  rw [quadraticHilbertConvolutionTrunc, quadraticHilbertTrunc]
  calc
    (∫ y, sharpQuadraticTailKernel lam ε (x - y) * f y) =
        ∫ t, s.indicator
          (fun u ↦ f (x - u) * phase (lam * u ^ 2) / (u : ℂ)) t := by
      simpa only [s, sharpQuadraticTailKernel, Set.indicator, sub_sub_cancel,
        Set.mem_setOf_eq, mul_comm, mul_left_comm, div_eq_mul_inv, mul_ite, mul_zero] using
        (integral_sub_left_eq_self
          (fun t : ℝ ↦ s.indicator
            (fun u ↦ f (x - u) * phase (lam * u ^ 2) / (u : ℂ)) t)
          volume x)
    _ = ∫ t in s, f (x - t) * phase (lam * t ^ 2) / (t : ℂ) :=
      integral_indicator hs

theorem cutoffBoundaryKernel_support_subset
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    support (cutoffBoundaryKernel lam ρ) ⊆ closedBall 0 (2 * ρ) := by
  intro t ht
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  by_contra h
  exact ht (cutoffBoundaryKernel_eq_zero_of_two_mul_le_abs lam hρ (le_of_not_ge h))

/-- Each smooth-to-sharp cutoff error contributes at most eight copies of the
project's measurable centered maximal function. -/
theorem cutoffBoundaryOperator_enorm_le_maximal
    (lam : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (f : ℝ → ℂ) (hf : Measurable f) (x : ℝ) :
    ‖∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y‖ₑ ≤
      8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  calc
    ‖∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y‖ₑ ≤
        ∫⁻ y, ‖cutoffBoundaryKernel lam ρ (x - y) * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in closedBall x (2 * ρ),
          ENNReal.ofReal (1 / ρ) * ‖f y‖ₑ := by
      rw [← lintegral_indicator measurableSet_closedBall]
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ closedBall x (2 * ρ)
      · simp only [Set.indicator_of_mem hy]
        rw [enorm_mul]
        apply mul_le_mul'
        · simpa only [← ofReal_norm] using
            ENNReal.ofReal_le_ofReal (cutoffBoundaryKernel_norm_le lam hρ)
        · exact le_rfl
      · simp only [Set.indicator, hy, ↓reduceIte]
        have hk : cutoffBoundaryKernel lam ρ (x - y) = 0 := by
          apply notMem_support.mp
          intro hmem
          apply hy
          have hs := cutoffBoundaryKernel_support_subset lam hρ hmem
          simpa [mem_closedBall, Real.dist_eq, abs_sub_comm] using hs
        simp [hk]
    _ = ENNReal.ofReal (1 / ρ) *
          ∫⁻ y in closedBall x (2 * ρ), ‖f y‖ₑ := by
      rw [MeasureTheory.lintegral_const_mul _ hf.enorm]
    _ = 4 * centeredAverage (2 * ρ) (fun y ↦ ‖f y‖ₑ) x := by
      unfold centeredAverage
      have hρ0 : ρ ≠ 0 := ne_of_gt hρ
      rw [show ENNReal.ofReal (1 / ρ) =
          4 / ENNReal.ofReal (2 * (2 * ρ)) by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp
        <;> ring]
      simp only [ENNReal.div_eq_inv_mul]
      ac_rfl
    _ ≤ 8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
      have h := centeredAverage_le_two_mul_centeredHardyLittlewoodMaximal
        (mul_pos (by norm_num : (0 : ℝ) < 2) hρ) (fun y ↦ ‖f y‖ₑ) x
      calc
        4 * centeredAverage (2 * ρ) (fun y ↦ ‖f y‖ₑ) x ≤
            4 * (2 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) :=
          mul_le_mul' le_rfl h
        _ = _ := by rw [← mul_assoc]; norm_num

                                                               
                                      
                                                      
         
                                            
          
                                                         
                           

                                                                         
                                                         
                                                               
       

                                                                          
                                                                   
                                                                      
                                       
                                                        
                                      
                                                 
                                                
                                                 
                                                                
                                                          
                      
           
                                                                     
                             
                                         
                                                                  
                                                                           
                                
                           
               
          
                                                
             
                                                         
                                                      
                                              
                                       
                                                           
                                                
             
                                         
                                                           
                                
                                                     
                                                                       
                                  
                  
                             
                                                                       
                                  
                  
                             
                                                           
                                                      
                                  
                                                                   
                                                       
                
                           

                                                                           
                                                             
                                                                
                                                                        
                                            
                                                         
                                                                   
                                    
                                                      
                                                                           
                                
                                          
                                             
                                             
                          
                                                               
                               
                                                 
                                                                
                          
                                                               
                               
                                                 
                                                                
                         
                                                           
                               
                                             
                                                            
                         
                                                           
                               
                                             
                                                            
                                 
      
                                                                           
                                                      
                                                  
                                              
                                                         
                             
                                                   
                                                                                 
                                                                           
                                                   
                                                    
                                                      
                                                           
                                                             
                                  
                                                                            
                                                                 
                                                    
                    
                                                        
                                                          
                                                      
                                                       
                                                              
                                                            
                                                         
                                                            
                                                                  
                                                                   
                                                          
                                                       
                                                              
                                                           
                                                          
                                                                   
                                                                   
                                                           
                                                               
                                                              
                                                    
         
               
                                                                    
                                                                  

                                                                         
                                                                            
                                                                          
                                    
                                                                         
                                         
                                                      
                                               
                                                     
                                                                    
                                
                                          
                                              
                                              
                                                            
                                                            
                                                           
                                                                   
                                             
                                             
                          
                                             
                                                 
                          
                                             
                                                 
                           
                                                         
                           
                                                         
                                                                           
                                          
      
                                                          
                                   
                                                
                                        
                                                        
                                       
            
                                 

                                                                    
                                                                   
                                        
                                                                      
                                                         

                                                
                                                
                                            
                                
                                                                    
                                                                            
                            
            
                                              

                                                            
                                                                 
                                           
                                                                                   
                                                         
                         
                                               
                                                                 
                                                  

                                                                    
                                                               
                                                                     
                                                                 
                                              
                                                     
                                                                    
                                                           
                                                                         
                                                                              


end QuadraticCarleson

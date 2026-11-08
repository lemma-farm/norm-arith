module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under the MIT-0 license. See ../../../../../third_party/twelfth/LICENSE-MIT-0.
Adapted from exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/SQUARE_KERNEL_NEAR_MANIFEST.json.
The imported DigammaSeries retains its separate Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Fourth.GammaShiftAmplitude
public import MathCollab.Density.Stronger.Fourth.SquareKernelFar
public import Mathlib
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set MeasureTheory
open MathCollab.Density.Stronger
open MathCollab.Density.Stronger.Fourth.Digamma
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem zetaGammaShiftError_le_quadratic
    {t c : ℝ} (ht : 4 ≤ t) (hc : 0 ≤ c) {w : ℂ} (u : ℝ)
    (hw : ‖w‖ ≤ c+|u|) :
    zetaGammaShiftError t w ≤ 17*c/4+c^2+u^2+17*|u|/4 := by
  have hnum : 17*‖w‖+2*‖w‖^2 ≤ 17*(c+|u|)+2*(c+|u|)^2 := by
    gcongr
  calc
    _ ≤ (17*(c+|u|)+2*(c+|u|)^2)/t :=
      div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ (17*(c+|u|)+2*(c+|u|)^2)/4 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) ht
    _ ≤ _ := by nlinarith [sq_nonneg (c-|u|), sq_abs u]

theorem exp_zetaGammaLeadingLog_vertical_le
    {t c : ℝ} (ht : 0 < t) (hc : 0 ≤ c) (u : ℝ) :
    Real.exp ((((c:ℂ)+(u:ℂ)*I)*zetaGammaLeadingLog t).re) ≤
      t^c * Real.exp (Real.pi*|u|/2) := by
  have hlog : Real.log (t/(2*Real.pi)) ≤ Real.log t :=
    Real.log_le_log (by positivity)
      (div_le_self ht.le (by linarith [Real.pi_gt_three]))
  rw [zetaGammaLeadingLog_mul_re]
  norm_num
  calc
    Real.exp (c*Real.log (t/(2*Real.pi))+u*(Real.pi/2)) ≤
        Real.exp (c*Real.log t+Real.pi*|u|/2) := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left hlog hc
      have h2 := mul_le_mul_of_nonneg_right (le_abs_self u) Real.pi_pos.le
      nlinarith
    _ = _ := by
      rw [Real.exp_add, Real.rpow_def_of_pos ht]
      congr 2
      ring

theorem exists_norm_zetaFourthKernel_near_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ,
      4 ≤ t → 4*c ≤ t → |u| ≤ t/4 →
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤
        K*t^c*Real.exp (-98*u^2) := by
  let D : ℝ := 17/4+Real.pi/2
  let A : ℝ := 101*c^2+17*c/4
  let Q : ℝ := 8*(1+c)+(8+D)^2/4
  let K : ℝ := (5625/c)*Real.exp A*Real.exp Q
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro t u ht hct hu
  have ht0 : 0 < t := by linarith
  let w : ℂ := (c:ℂ)+(u:ℂ)*I
  let R : ℝ := 1+c+|u|
  let E : ℝ := 17*c/4+c^2+u^2+17*|u|/4
  have hw : ‖w‖ ≤ c+|u| := norm_vertical_shift_le hc.le u
  have hwsmall : ‖w‖ ≤ t/2 := hw.trans (by linarith)
  have hwre : 0 ≤ w.re := by dsimp [w]; norm_num; exact hc.le
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg u]
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤ 625*R^8 :=
    norm_hughesYoungAuxiliaryZero_le_polynomial hR (hw.trans (by dsimp [R]; linarith))
  have hpole := norm_zetaSquarePoleShift_le ht0 hwsmall
  have herr : zetaGammaShiftError t w ≤ E :=
    zetaGammaShiftError_le_quadratic ht hc.le u hw
  have hlead := exp_zetaGammaLeadingLog_vertical_le ht0 hc.le u
  have hgamma :
      ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ ≤
      Real.exp E * (t^c*Real.exp (Real.pi*|u|/2)) := by
    exact (norm_gammaReal_shift_sq_le_exp ht hwre hwsmall).trans
      (mul_le_mul (Real.exp_le_exp.mpr herr) hlead
        (Real.exp_pos _).le (Real.exp_pos _).le)
  have hwlower : c ≤ ‖w‖ := vertical_shift_re_le_norm hc.le u
  have hpoly : R^8*Real.exp (D*|u|) ≤ Real.exp Q*Real.exp (u^2) := by
    simpa [R,Q] using
      abs_polynomial_mul_exp_le_gaussian (by linarith : 0 ≤ 1+c)
        (by norm_num : (0:ℝ) ≤ 1) D 8 u
  have hexp :
      Real.exp (100*c^2-100*u^2)*Real.exp E*Real.exp (Real.pi*|u|/2) =
        Real.exp A*Real.exp (D*|u|)*Real.exp (-99*u^2) := by
    simp only [← Real.exp_add]
    congr 1
    dsimp [A,D,E]
    ring
  have hg : Real.exp (u^2)*Real.exp (-99*u^2) = Real.exp (-98*u^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [norm_zetaFourthKernel_vertical]
  change Real.exp (100*c^2-100*u^2)*‖hughesYoungAuxiliaryZero w‖*
    ‖zetaSquarePoleShift t w‖*
    ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
      Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖/‖w‖ ≤ _
  calc
    _ ≤ Real.exp (100*c^2-100*u^2)*(625*R^8)*9*
        (Real.exp E*(t^c*Real.exp (Real.pi*|u|/2)))/c := by
      gcongr
    _ = (5625/c)*t^c*R^8*
        (Real.exp (100*c^2-100*u^2)*Real.exp E*Real.exp (Real.pi*|u|/2)) := by ring
    _ = (5625/c)*t^c*Real.exp A*(R^8*Real.exp (D*|u|))*Real.exp (-99*u^2) := by
      rw [hexp]
      ring
    _ ≤ (5625/c)*t^c*Real.exp A*(Real.exp Q*Real.exp (u^2))*Real.exp (-99*u^2) := by
      gcongr
    _ = K*t^c*(Real.exp (u^2)*Real.exp (-99*u^2)) := by dsimp [K]; ring
    _ = _ := by rw [hg]

                                                              
                               
                       
                                            
                                      
                                                                
                                                              
                               
                  
                                 
                         
                                                           
                                                         
                                                             
        
                                                     
                                    
              
                               
                                                          
                                                             

                                                      
                                               
                                                                      
                                                       
                                                                 
                                                                            
                                                                                 
                                                          

                                                                       
                             
                       
                                                       
                                          
                                                            
                  
                
                                                                 
                                                                            
      
                                            
                                                                            
                                    
                                                          


end MathCollab.Density.Stronger.Fourth

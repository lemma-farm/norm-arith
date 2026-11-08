/-
# Parameterized contour integrals (L4.2a)

Contour integrals along a parameterized closed curve `γ : ℝ → ℂ`, defined as the interval
integral `∫ t in 0..2π, deriv γ t • f (γ t)`.  This is exactly the shape of Mathlib's
`circleIntegral` (the special case `γ = circleMap c R`), so the circle results of
`CircleCauchy.lean` transfer by `rfl`, while general smooth boundaries of convex domains — the
contours of the Crouzeix–Palencia argument — become available.

## Main declarations

* `ContourIntegrable f γ` — integrability of `t ↦ deriv γ t • f (γ t)` on `[0, 2π]`.
* `contourIntegral f γ` — the contour integral `∫ t in 0..2π, deriv γ t • f (γ t)`.
* `contourIntegral_circleMap`, `contourIntegrable_circleMap_iff` — agreement with Mathlib's
  `circleIntegral` / `CircleIntegrable` for `γ = circleMap c R`.
* `ContourIntegrable.of_continuousOn` — continuity of the curve derivative and of `f` on the
  trace gives integrability.
* `contourIntegral_add`, `contourIntegral_sub`, `contourIntegral_neg`, `contourIntegral_smul` —
  linearity in the integrand.
* `ContinuousLinearMap.contourIntegral_comp_comm`, `contourIntegral_const_mul`,
  `contourIntegral_mul_const` — continuous linear maps and constant algebra factors commute
  with the integral.
* `norm_contourIntegral_le_of_norm_le_const` — the length-type bound `‖∫‖ ≤ 2π C`.
* `contourIntegral_eq_sub_of_hasDerivAt`, `contourIntegral_eq_zero_of_hasDerivAt_of_closed` —
  the fundamental theorem of calculus along `γ`: an integrand with a global primitive
  integrates to the boundary difference, hence to `0` along a closed curve (Cauchy's theorem
  for integrands with a primitive).
-/
import Mathlib

open scoped Real Interval
open MeasureTheory Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `f` is integrable along the parameterized curve `γ` over `[0, 2π]`: the integrand
`t ↦ deriv γ t • f (γ t)` is interval integrable. -/
def ContourIntegrable (f : ℂ → F) (γ : ℝ → ℂ) : Prop :=
  IntervalIntegrable (fun t => deriv γ t • f (γ t)) volume 0 (2 * π)

/-- The contour integral `∫ t in 0..2π, γ'(t) • f (γ t)` of `f` along the parameterized curve
`γ`. -/
noncomputable def contourIntegral (f : ℂ → F) (γ : ℝ → ℂ) : F :=
  ∫ t in (0 : ℝ)..(2 * π), deriv γ t • f (γ t)

                                                                                       
                    
                                                               
                                                                   

                                                                                        
                      
                                                                     
                                                                   
                               

                                                                                       
              
theorem ContourIntegrable.of_continuousOn {f : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc 0 (2 * π))) (hγ' : ContinuousOn (deriv γ) (Icc 0 (2 * π)))
    (hf : ContinuousOn f (γ '' Icc 0 (2 * π))) : ContourIntegrable f γ := by
  unfold ContourIntegrable
  rw [← uIcc_of_le Real.two_pi_pos.le] at hγ hγ' hf
  exact (hγ'.smul (hf.comp hγ (mapsTo_image _ _))).intervalIntegrable

                                                                                  
                                  
                                                                                            
                        
                      
                                           

                                                     
                                                                  
                        
                      
                                     

theorem contourIntegral_sub {f g : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ)
    (hg : ContourIntegrable g γ) :
    contourIntegral (fun z => f z - g z) γ = contourIntegral f γ - contourIntegral g γ := by
  unfold contourIntegral
  simp only [smul_sub]
  exact intervalIntegral.integral_sub hf hg

                                                              
                                                                        
                        
                                                                                   
                                   
        
                                          

section Linearity

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Continuous complex-linear maps commute with contour integrals. -/
theorem ContinuousLinearMap.contourIntegral_comp_comm [CompleteSpace F] [CompleteSpace G]
    (L : F →L[ℂ] G)
    {f : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => L (f z)) γ = L (contourIntegral f γ) := by
  unfold contourIntegral
  simpa only [Function.comp_apply, map_smul] using L.intervalIntegral_comp_comm hf

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- A constant left factor moves through a contour integral in a complex Banach algebra. -/
theorem contourIntegral_const_mul {f : ℂ → B} {γ : ℝ → ℂ} (b : B)
    (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => b * f z) γ = b * contourIntegral f γ := by
  let L : B →L[ℂ] B := ContinuousLinearMap.mul ℂ B b
  simpa only [L, ContinuousLinearMap.mul_apply'] using L.contourIntegral_comp_comm hf

/-- A constant right factor moves through a contour integral in a complex Banach algebra. -/
theorem contourIntegral_mul_const {f : ℂ → B} {γ : ℝ → ℂ} (b : B)
    (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => f z * b) γ = contourIntegral f γ * b := by
  let L : B →L[ℂ] B := (ContinuousLinearMap.mul ℂ B).flip b
  simpa only [L, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
    L.contourIntegral_comp_comm hf

end Linearity

                                                                                  
                                                        
                                                                                
                                                                
                                           
                        
      
                                                                          
                                                                              
                                              
                                        
                       
                                               
          

                                                                                          
                                                                                          
                                                                                         
                                                            
                                                                   
                                    
                                                         
                                  
                        
                                                       
                                                  
                                          
                                              

                                                                                          
                                                    
                                                                                  
                                                            
                                                                   
                                                                
                                 
           
                                      
                                        
                                                                           
                                           
                                                                                         
               

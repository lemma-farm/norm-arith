module

public import RequestProject.Euler.ContourCompactSmoothIntegral
public import RequestProject.Euler.ContourDerivativeLower
public import RequestProject.Euler.ContourSmoothEmbedding
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The genuine smooth extension of a normalized contour chord

The extension is the actual integral of the actual derivative along the
unit segment.  The fundamental theorem of calculus identifies it with
the divided chord away from zero and with the derivative at zero.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric MeasureTheory Complex
open scoped ContDiff

namespace Euler2D

def smoothContourNormalizedChord (z : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, deriv z (θ + u * τ)

@[simp] theorem smoothContourNormalizedChord_zero (z : ℝ → ℂ) (θ : ℝ) :
    smoothContourNormalizedChord z θ 0 = deriv z θ := by
  simp [smoothContourNormalizedChord, intervalIntegral.integral_const]

/-- The actual FTC identity, including the degenerate chord at zero. -/
theorem smul_smoothContourNormalizedChord {z : ℝ → ℂ} (hz : ContDiff ℝ 1 z) (θ τ : ℝ) :
    τ • smoothContourNormalizedChord z θ τ = z (θ + τ) - z θ := by
  have hc : ContinuousOn (fun u : ℝ => deriv z (θ + u • τ)) (Icc 0 1) :=
    (hz.continuous_deriv_one.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
  simpa only [smul_eq_mul, smoothContourNormalizedChord] using
    (intervalIntegral.integral_unitInterval_deriv_eq_sub
      (𝕜 := ℝ) (f := z) (f' := deriv z) (z₀ := θ) (z₁ := τ) hc
      (fun u _ => (hz.differentiable_one (θ + u • τ)).hasDerivAt))

                                                                             
                                  
                                                                          
                                                        
                                                     
                                                   

                                                                              
                                                                                 
                                                                                
                                                                         
                                                
                                       
                                                                       
                                                                                            
                                                           
                              
                                                                        
                                                                            
            
                                                                                  
                                   
          
          

                                                                               
                                                      
                                                                                       
                                                            
         
                                     
                                       
           
            
                                                                           

                                                                      
                                                            
theorem norm_smoothContourNormalizedChord_lower {z : ℝ → ℂ} (hz : ContDiff ℝ 1 z) {c : ℝ}
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (θ τ : ℝ) (hτ : |τ| ≤ Real.pi) : c ≤ ‖smoothContourNormalizedChord z θ τ‖ := by
  by_cases hzero : τ = 0
  · subst τ
    rw [smoothContourNormalizedChord_zero]
    exact norm_hasDerivAt_lower_of_chord (hz.differentiable_one θ).hasDerivAt
      Real.pi_pos (hchord θ)
  · have hh := hchord θ τ hτ
    have he : ‖z θ - z (θ + τ)‖ = |τ| * ‖smoothContourNormalizedChord z θ τ‖ := by
      rw [norm_sub_rev, ← smul_smoothContourNormalizedChord hz θ τ, norm_smul, Real.norm_eq_abs]
    rw [he, mul_comm c] at hh
    exact le_of_mul_le_mul_left hh (abs_pos.mpr hzero)

                                                                                      
                
                                                                     
                                                                              
                                                                                          

                                                                       
                                                      
                                                                    
                                              
                                                                     
                                        
                                                                                               
                                                                                           
                                                                             
                             

                                                                    
                                                                         

                                                              
                                                                              
                                               
                                                 
                                                                                     
                                                
                                                              

                                                                   
                                                                         
                                                                           
                                                         
                             
                                                                  
                                                                  
                                        
                                    
                                                                       
                                                                                         
                                                                                         
                                            
                                                         
                                                              
                                                                                            
                                                                   
                                                                                          

end Euler2D

end

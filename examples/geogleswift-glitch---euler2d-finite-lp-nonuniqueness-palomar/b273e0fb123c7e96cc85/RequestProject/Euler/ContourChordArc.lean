module

public import RequestProject.Euler.AreaChart
public import RequestProject.Euler.ContourHolderSpace

/-!
# Actual chord bounds and injectivity near a reference circle

The circular bound is derived from the complex exponential chord formula
and the sine inequality on a half-period.  The perturbation bound uses
the true derivative and the mean value theorem.  Short representatives
then identify the quotient-circle metric with the relevant angular gap.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric Real
open scoped ContDiff NNReal

namespace Euler2D

                                                   
                                                                            
                                                                                
                                     
                          
           
             
        
                                                                   
                                                                                 
                                
                  
                                                                                 
                                                         
                                                                                                             
      

                                                                               
                                                                 
                                                           
                                                        
             
      
                                                 
                                                          
          
                                                                                          
                                               

theorem norm_sub_le_of_contDiff_deriv_bound {p : ℝ → ℂ} {ε : ℝ}
    (hp : ContDiff ℝ 1 p) (hε : 0 ≤ ε) (hderiv : ∀ t, ‖deriv p t‖ ≤ ε) (θ φ : ℝ) :
    ‖p θ - p φ‖ ≤ ε * |θ - φ| := by
  have hnn (t : ℝ) : ‖deriv p t‖₊ ≤ NNReal.mk ε hε := by
    exact_mod_cast hderiv t
  have hLip := lipschitzWith_of_nnnorm_deriv_le (hp.differentiable one_ne_zero) hnn
  simpa only [NNReal.coe_mk, Real.norm_eq_abs] using hLip.norm_sub_le θ φ

                                                                 
                                                   
                                                            
                               
                                                           
                                            
                                                                      
                                           
                                                                              
                          
                                                               
                   
           

                                                                            
                                                   
                                                            
                          
                                                                   
                                                                   
                                     
                                                      
                                                                                               
                                                                       

                                                                                     
                                                             
                             
                                                          
                                                                        
                            
                                                 
                                                                   
                                                                          
                        

                                                                     
                                               
theorem exists_short_contour_representatives (x y : ContourCircle) :
    ∃ θ φ : ℝ, (θ : ContourCircle) = x ∧ (φ : ContourCircle) = y ∧
      |θ - φ| ≤ π ∧ dist x y = |θ - φ| := by
  let δ : ℝ := (AddCircle.equivIco (2 * π) (-π) (x - y) : ℝ)
  let φ : ℝ := (AddCircle.equivIco (2 * π) 0 y : ℝ)
  let θ : ℝ := φ + δ
  have hδcoe : (δ : ContourCircle) = x - y :=
    (AddCircle.equivIco (2 * π) (-π)).symm_apply_apply (x - y)
  have hφcoe : (φ : ContourCircle) = y :=
    (AddCircle.equivIco (2 * π) 0).symm_apply_apply y
  have hθcoe : (θ : ContourCircle) = x := by
    dsimp only [θ]
    rw [AddCircle.coe_add, hφcoe, hδcoe]
    abel
  have hδlo : -π ≤ δ := (AddCircle.equivIco (2 * π) (-π) (x - y)).property.1
  have hδhi : δ < -π + 2 * π := (AddCircle.equivIco (2 * π) (-π) (x - y)).property.2
  have hδabs : |δ| ≤ π := abs_le.mpr ⟨hδlo, by linarith⟩
  have hsub : θ - φ = δ := by dsimp only [θ]; abel
  have hn : ‖(δ : ContourCircle)‖ = |δ| :=
    (AddCircle.norm_coe_eq_abs_iff (2 * π) (by positivity)).mpr (by
      rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      nlinarith)
  refine ⟨θ, φ, hθcoe, hφcoe, ?_, ?_⟩
  · rw [hsub]
    exact hδabs
  · rw [dist_eq_norm, ← hδcoe, hn, hsub]

                                                                  
                           
                                                                            
                                                                                          
                           
                                                  
                                                                                  
                                                                   
                                                                             
                                      
                               
             

                                                                                
                                                                                                 
                                                                        
                              
                             
                                            
                                                                                      
                                                      
                                                                                          
         

                                                            
                                                      
                           
                                                                            
                                                                                            
                              
               
                                                         
                                     
                                                      
                                                                                                
                          

                                                                    
                                                      
                           
                                                                            
                                                                                            
                                   
                                                                   
                                                                         

end Euler2D

end

module

public import Mathlib

/-!
# Exponentially decaying Fourier multipliers (Lemma `pc:smoothing`)

For a complete complex normed space `V` (for the paper, `V = ℂⁿ` and the `E_m` are matrices),
a `V`-valued function `f` on the circle `ℝ / 2πℤ` has Fourier coefficients
`f̂(m) = (2π)⁻¹ ∫₀^{2π} e^{-imθ} f(θ) dθ`. Given bounded operators `E_m`, the multiplier is
`(E f)(θ) = ∑_m e^{imθ} E_m f̂(m)`.

* `fourierMultiplier_contDiff`, `fourierMultiplier_iteratedDeriv_le`: if
  `‖E_m‖ ≤ w(m)` with `∑_m (1+|m|)^j w(m) < ∞` for all `j`, then `E f` is smooth and
  `‖(E f)^{(j)}‖_∞ ≤ (∑_m (1+|m|)^j w(m)) ‖f‖_∞`; in particular `E : C⁰ → C^r` is bounded for
  every finite `r`.
* `exp_decay_weight_summable`: the weights `C (1+|m|)^k a₀^{|m|}`, `0 < a₀ < 1`, qualify
  (`smoothing_multiplier`).
* `smoothing_multiplier_tail`: the truncations `E_{≤n}` (finite rank when `V` is finite
  dimensional) converge to `E` in the operator norm `C⁰ → C^r`; this is the compactness
  statement of the lemma, here in the `C⁰ → C^r` form.
* `modified_weight`: the same conclusions hold when finitely many `E_m` are changed
  arbitrarily.
* The paper states compactness on the little-Hölder space `c^{1,γ}`; here it is proved as
  operator-norm approximation by finite-rank truncations from `C⁰` into `C^r`
  (`fourierMultiplier_eq_sum_add_tail`, `smoothing_multiplier_tail`), which is the key step
  of the paper's argument. The space `c^{1,γ}` itself is not formalized.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real Complex

namespace Euler2D

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

                         
                       
                                                                              
                             

omit [CompleteSpace V] in
/-- `|e^{-imθ}| = 1`. -/
lemma norm_cexp_neg_int_mul_I (m : ℤ) (θ : ℝ) : ‖cexp (-((m : ℂ) * θ * I))‖ = 1 := by
  rw [Complex.norm_exp]; simp

                         
                                                                   
                                                               
                                                                 
                                                            
                                 
                
                
                           
                                                                      
                                                                                  
             
                                                              
                                                        
                                                                                 
                                                                                       
                        
                   
                                                                
                 
           
        

                         
                                 
                                                           
                                                                
                                                                 
                                                                 
                                                                        
                                     
                                

                                                                                              
noncomputable def fourierCoeffV (f : ℝ → V) (m : ℤ) : V :=
  ((2 * π)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * π, cexp (-((m : ℂ) * θ * I)) • f θ

                                                              
                                                                                       
                                                  

                                                                 
                                                                                  
                                  

omit [CompleteSpace V] in
/-- `‖f̂(m)‖ ≤ M` whenever `‖f‖ ≤ M` on `[0, 2π]`. -/
lemma norm_fourierCoeffV_le {f : ℝ → V} {M : ℝ} (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M)
    (m : ℤ) : ‖fourierCoeffV f m‖ ≤ M := by
  have hint : ‖∫ θ in (0 : ℝ)..2 * π, cexp (-((m : ℂ) * θ * I)) • f θ‖ ≤ M * |2 * π - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ hθ
    rw [Set.uIoc_of_le (by positivity)] at hθ
    rw [norm_smul, norm_cexp_neg_int_mul_I, one_mul]
    exact hf θ ⟨hθ.1.le, hθ.2⟩
  have hpi : 0 < 2 * π := by positivity
  rw [fourierCoeffV, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpi.le)]
  rw [sub_zero, abs_of_pos hpi] at hint
  calc (2 * π)⁻¹ * ‖_‖ ≤ (2 * π)⁻¹ * (M * (2 * π)) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hpi.le)
    _ = M := by field_simp

                         
                                                                              
                                                                                   
                                                                                 
                             
                                                                                       
                                                                         
                                                  
                                                               
                                            
                                                
                       
                                                                                           
                                                            
                                                  
                                                   
                                                                                     
                                                        
                    

                                                                                  
                                                                                           
                                                                          
                                                                                 
                                                                                
                                              
                          
                                                                                         
                                                                        

                                                                          
                                                                   
                                                                                  
                                                                                 
                                                                                       
                                                 
                                                     
                                                  
                          
                                                                                        
                                     
                                     
                                                                                
                       
                                                          
                                                                  

                                               
                                                                                    
                                                          
                                                                                 
                                                          
                                                                                            
                                                                        
                                    
                                                               
                                          
             
                                                          
                                                      
                                                          
               
                                                  
                                                                                              
                                          
                                                                                       
                                                                         
                                                     
                    

                                                                                            
               
                                                                                      
                                                                                               
                                                                          
                                                              
                              
                                
                                                                  
        
                                
                                                                                     
                         
        

                                               
                                                                                     
                          

                         
                                      
                                                                    
                                                                                 
                                                              
                                                             
                  

                                                                                           
                     
                                                                                 
                                                                                 
                                                
                             
                                                                                   
                                                       
                                                                                             
                                                       
                                                                                  
           
                                   
                      
                                                                                
                                                                       
                                        
                                                                                                       
                                                     
                                                      
                          
                                          
      

                                                                                           
                                                                                             
                                                                                        
                                                         
                                                                         
                                                                                 
                                                                               
                                                                                          
                                                                         
                                                                                            
                       
                                                                  
                            
                                                               
                                          
            
                  
             
                                                                          
                 
              
                                                  
                 
                                                                        
                      
                                                                                  
                                   
                                                                                        
                                
                       
               
               

                                                                                                 
                                                 
                                                                                                 
                                                                   
                                                                   
                                                      
                                                                    
                                                                                        
                                                                                     
                                                                                     

                         
                                                                                             
                                                                                             
                 
                                                                                          
                                       
                                                                       
                                        
                                                                     
                                                                               
                       
                             
                                             
                                                               
                                                                                            
                                                                         
                   
                            
                                 
                                                      

end Euler2D

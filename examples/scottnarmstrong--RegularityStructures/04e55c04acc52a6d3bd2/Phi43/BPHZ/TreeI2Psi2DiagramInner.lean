/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramKernel

/-!
# Integrals of the kernel increment against singular weights

With `A(w) = K(y - w) - K(x - w)` and `r = s(y - x)`:

* `i2Psi2LintBound_kernel_sub_two`: `∫ |A(w)| s(g - w)^(-2) dw ≲ B r^θ (s(y - g)^(-θ) + s(x - g)^(-θ))`
  for `θ ∈ (0, 1]`;
* `i2Psi2LintBound_kernel_sub_three`: `∫ |A(w)| s(g₁ - w)^(-1) s(g₂ - w)^(-κ) dw ≲
  B r^θ (s(y - g₂)^(-(θ+κ-1)) + s(x - g₂)^(-(θ+κ-1)) + 2 s(g₁ - g₂)^(-(θ+κ-1)))` for
  `θ ∈ [0, 1)` and `θ + κ > 1`;
* `i2Psi2LintBound_kernel_sub_slab`: `∫ |A(w)| s(g₁ - w)^(-λ₁) s(g₂ - w)^(-λ₂) dw ≲ B r^θ` when
  `3 + θ + λ₁ + λ₂ < 5` (no singular output), under the support hypotheses.

The constants depend only on the exponents.  [Hai14, Lemma 10.14, Lemma 10.18].
-/

public section

open MeasureTheory

namespace RegularityStructures

private theorem measurable_weight_mul (p g : SpaceTime) (a b : ℝ) :
    Measurable fun w : SpaceTime => torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  (measurable_torusParabolicSize_sub_rpow p a).mul (measurable_torusParabolicSize_sub_rpow g b)

private theorem weight_mul_nonneg (p g : SpaceTime) (a b : ℝ) (w : SpaceTime) :
    0 ≤ torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)

/-- **Increment of `K` against `s(g - w)^(-2)`**, [Hai14, Lemma 10.14 and 10.18]. -/
theorem i2Psi2LintBound_kernel_sub_two {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      ∀ x y g : SpaceTime, 0 < torusParabolicSize (y - g) → 0 < torusParabolicSize (x - g) →
        i2Psi2LintBound volume (fun w => |K (y - w) - K (x - w)| *
          torusParabolicSize (g - w) ^ (-(2 : ℝ)))
          (C * B * torusParabolicSize (y - x) ^ θ *
            (torusParabolicSize (y - g) ^ (-θ) + torusParabolicSize (x - g) ^ (-θ))) := by
  obtain ⟨CG, hCG, hG⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := 3 + θ) (b := 2)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith)
  refine ⟨12 * CG, by positivity, ?_⟩
  intro K B hB hKb hKi x y g hyg hxg
  have e : (5 : ℝ) - (3 + θ) - 2 = -θ := by ring
  have gy := hG y g hyg
  have gx := hG x g hxg
  rw [e] at gy gx
  have s := gy.add (g := fun w => torusParabolicSize (x - w) ^ (-(3 + θ)) *
      torusParabolicSize (g - w) ^ (-(2 : ℝ))) (measurable_weight_mul y g _ _).aemeasurable
    (weight_mul_nonneg y g _ _) (weight_mul_nonneg x g _ _)
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) gx
  have c := s.const_mul (c := 12 * B * torusParabolicSize (y - x) ^ θ)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
    with w hy hx
  have h := abs_kernel_sub_le hB hθ.le hθ1 hKb hKi (x := x) (y := y) (w := w) hy hx
  have n2 : 0 ≤ torusParabolicSize (g - w) ^ (-(2 : ℝ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  calc |K (y - w) - K (x - w)| * torusParabolicSize (g - w) ^ (-(2 : ℝ))
      ≤ (12 * B * torusParabolicSize (y - x) ^ θ * (torusParabolicSize (y - w) ^ (-(3 + θ)) +
        torusParabolicSize (x - w) ^ (-(3 + θ)))) * torusParabolicSize (g - w) ^ (-(2 : ℝ)) :=
        mul_le_mul_of_nonneg_right h n2
    _ = _ := by ring

                                                                                               
                                                                                           
                                     
                                                           
                                                  
                                                        
                                                    
                                                         
                                                                                             
                                                                
                                                                            
                                                                  
                                                                                          
                                                   
                                                           
                                                            
                                                                       
                                                                                   
                                                    
                                     
                                         
                                                          
                       
                       
                        
                    
                                                 
                                                                                 
                                         
                                                                  
                                                                           
                                                                                              
                                                                       
                                                                       
                                                                       
                                                                                                  
          
                                                                      
                                                                                   
                                          
                                                                                   
                                                                                              
                                                                                      
                                                                                                
                                 
                                                                                                 
           
                                                                                                 
           
                                          
                  
                                                                                                      
                                              
                                              
                                                                            
                                             
                                                                                             
                                                                                               
                                                                                
                                                 
                                                                                             
                                                
                                                                                              
                                                          
                                                 
                                                                                               
                                                
                                                                                                
                                                     
                                                                       
                                                             
                                
                    

                                                                       
                                                                                                
                                               
                                                           
                                              
                                                  
                                                        
                                                    
                                                         
                                                                                             
                                                                                      
                                                                  
                                                                                      
                                                        
                                                                                         
                                                     
                                     
                                                
                                           
                                       
                                       
                                       
                                                                              
                                                                                      
                                                        
                                                                                    
                                                        
                                                    
                                                      
                                                                                      
                                                          
                                                                                
                                                                                          
                                                         
                                                    
                                                                                      
                                                                                       
                                                                      
                                                                                   
                                          
                                                                                   
                  
                                                                     
                                                                                            
                                 
                                                                       
                                              
                                                                      
                                                                                               
                                                                                        
                                       
                    

end RegularityStructures

end

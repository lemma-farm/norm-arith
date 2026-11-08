/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneCross
public import Phi43.BPHZ.TreeI3Psi2ChaosOnePotPair

/-!
# Convolution estimates for potentials with general kernel exponents

Generalisations of `power_mul_abs_J_le`, `abs_J_mul_J_le` and `integral_pot_mul_pot_le` of the
chaos-`1` part of `I(Ψ³)Ψ²` to kernels `J` with `|J| ≤ B s^(-j)` of possibly different orders
`j` (the kernel `J_a` of order `3` and the kernel difference `ΔJ` of order `3 + θ`), and to two
different kernels in the pairing of two potentials.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- `∫ s(c - y)^(-a) |J(w - y)| dy ≤ C B s(c - w)^(5-a-j)` for `|J| ≤ B s^(-j)`. -/
theorem power_mul_abs_J_le_gen {a j : ℝ} (ha : 0 < a) (ha5 : a < 5) (hj : 0 < j)
    (hj5 : j < 5) (haj : 5 < a + j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ B * torusParabolicSize x ^ (-j)) →
      ∀ c w : SpaceTime, 0 < torusParabolicSize (c - w) →
        Integrable (fun y => singularPow a c y * |J (w - y)|) ∧
          ∫ y, singularPow a c y * |J (w - y)| ≤ C * B * torusParabolicSize (c - w) ^ (5 - a - j) := by
  obtain ⟨C, hC, h⟩ := integrable_and_integral_singularPow_mul_le (a := a) (b := j)
    ha ha5 hj hj5 haj
  refine ⟨C, hC, fun {J B} hB hJm hJ c w hcw => ?_⟩
  obtain ⟨i, b⟩ := h c w hcw
  have hmaj : Integrable (fun y => B * (singularPow a c y * singularPow j w y)) := i.const_mul _
  have hm : Measurable (fun y => singularPow a c y * |J (w - y)|) :=
    (measurable_singularPow a c).mul
      (continuous_abs.measurable.comp (hJm.comp (measurable_const.sub measurable_id)))
  have hle : ∀ᵐ y : SpaceTime ∂volume, singularPow a c y * |J (w - y)| ≤
      B * (singularPow a c y * singularPow j w y) := by
    filter_upwards [ae_torusParabolicSize_sub_pos w] with y a'
    have := mul_le_mul_of_nonneg_left (hJ _ a') (singularPow_nonneg a c y)
    refine this.trans (le_of_eq ?_)
    unfold singularPow
    ring
  refine ⟨Integrable.mono' hmaj hm.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hle] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (singularPow_nonneg _ _ _) (abs_nonneg _))]
    exact hy
  · calc ∫ y, singularPow a c y * |J (w - y)| ≤ ∫ y, B * (singularPow a c y * singularPow j w y) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
            mul_nonneg (singularPow_nonneg _ _ _) (abs_nonneg _)) hmaj hle
      _ = B * ∫ y, singularPow a c y * singularPow j w y := by rw [integral_const_mul]
      _ ≤ B * (C * torusParabolicSize (c - w) ^ (5 - a - j)) :=
          mul_le_mul_of_nonneg_left b hB
      _ = _ := by ring

                                                                     
                                                     
                                                                       
                                                                             
                                     
                                                                                    
                                                                                    
                                                           
                                                            
                                             
                                                                           
                                                                                     
                        
                                                                            
                             
                                                                                           
                 
                                                                 
                                                                                         
                                                                                       
                                                                     
                                                                
                                                                                                   
                                                                           
                                  
                                   
                      
        
                                                               
                                  
                                                                                   
            
                                            
                                                                      
                                                                       
                                                              
                                                                                               
                                                                        
                                                          
                      

                                                                    
                                                                          
                                                                                         
                                                                        
                                                                         
                                                  
                                                               
                                                          
                                                   
                                                                                   
                                                     
                                                                 
                                                          
                                                                                  
                                                                                   
                                         
                                                               
                                                         
                                   
                                                                                            
                                       
                                                               
                                                        
                                                                              
                                         
                                                               
                                                         
                                      
                                                                            
                                                                                              
                      

end RegularityStructures

end

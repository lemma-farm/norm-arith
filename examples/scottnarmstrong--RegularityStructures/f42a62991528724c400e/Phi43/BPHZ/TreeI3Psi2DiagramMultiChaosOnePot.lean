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

                                                                                   
                                                                                
                                     
                                                                          
                                                                                 
                                                         
                                                               
                                                                                                       
                                                                                   
                     
                                                   
                            
                                                                                                
                                                                    
                                    
                                                                                      
                                                                        
                                                       
                                                              
                                                                          
                                   
                      
        
                                                               
                                  
                                                                                               
            
                                                                                                   
                                                                       
                                                                          
                                                                                      
                                                               
                                        
                      

/-- `∫ |J₁(w - y)| |J₂(w' - y)| dy ≤ C B₁ B₂ s(w - w')^(5-j₁-j₂)`. -/
theorem abs_J_mul_J_le_gen {j₁ j₂ : ℝ} (hj₁ : 0 < j₁)
    (hj₁5 : j₁ < 5) (hj₂ : 0 < j₂) (hj₂5 : j₂ < 5) (hj : 5 < j₁ + j₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J₁ J₂ : SpaceTime → ℝ} {B₁ B₂ : ℝ}, 0 ≤ B₁ → 0 ≤ B₂ →
      Measurable J₁ → Measurable J₂ →
      (∀ x, 0 < torusParabolicSize x → |J₁ x| ≤ B₁ * torusParabolicSize x ^ (-j₁)) →
      (∀ x, 0 < torusParabolicSize x → |J₂ x| ≤ B₂ * torusParabolicSize x ^ (-j₂)) →
      ∀ w w' : SpaceTime, 0 < torusParabolicSize (w - w') →
        Integrable (fun y => |J₁ (w - y)| * |J₂ (w' - y)|) ∧
          ∫ y, |J₁ (w - y)| * |J₂ (w' - y)| ≤
            C * B₁ * B₂ * torusParabolicSize (w - w') ^ (5 - j₁ - j₂) := by
  obtain ⟨C, hC, h⟩ := integrable_and_integral_singularPow_mul_le (a := j₁) (b := j₂)
    hj₁ hj₁5 hj₂ hj₂5 hj
  refine ⟨C, hC, fun {J₁ J₂ B₁ B₂} hB₁ hB₂ hJ₁m hJ₂m hJ₁ hJ₂ w w' hww => ?_⟩
  obtain ⟨i, b⟩ := h w w' hww
  have hmaj : Integrable (fun y => B₁ * B₂ * (singularPow j₁ w y * singularPow j₂ w' y)) :=
    i.const_mul _
  have hm : Measurable (fun y => |J₁ (w - y)| * |J₂ (w' - y)|) :=
    (continuous_abs.measurable.comp (hJ₁m.comp (measurable_const.sub measurable_id))).mul
      (continuous_abs.measurable.comp (hJ₂m.comp (measurable_const.sub measurable_id)))
  have hle : ∀ᵐ y : SpaceTime ∂volume, |J₁ (w - y)| * |J₂ (w' - y)| ≤
      B₁ * B₂ * (singularPow j₁ w y * singularPow j₂ w' y) := by
    filter_upwards [ae_torusParabolicSize_sub_pos w, ae_torusParabolicSize_sub_pos w'] with y a' b'
    have := mul_le_mul (hJ₁ _ a') (hJ₂ _ b') (abs_nonneg _) (mul_nonneg hB₁
      (singularPow_nonneg j₁ w y))
    refine this.trans (le_of_eq ?_)
    unfold singularPow
    ring
  refine ⟨Integrable.mono' hmaj hm.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hle] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact hy
  · calc ∫ y, |J₁ (w - y)| * |J₂ (w' - y)| ≤
          ∫ y, B₁ * B₂ * (singularPow j₁ w y * singularPow j₂ w' y) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _)) hmaj hle
      _ = B₁ * B₂ * ∫ y, singularPow j₁ w y * singularPow j₂ w' y := by rw [integral_const_mul]
      _ ≤ B₁ * B₂ * (C * torusParabolicSize (w - w') ^ (5 - j₁ - j₂)) :=
          mul_le_mul_of_nonneg_left b (mul_nonneg hB₁ hB₂)
      _ = _ := by ring

                                                                    
                                                                          
                                                                                         
                                                                        
                                                                         
                                                  
                                                               
                                                          
                                                   
                                                                                   
                                                     
                                                                 
                                                          
                                                                                  
                                                                                   
                                         
                                                               
                                                         
                                   
                                                                                            
                                       
                                                               
                                                        
                                                                              
                                         
                                                               
                                                         
                                      
                                                                            
                                                                                              
                      

end RegularityStructures

end

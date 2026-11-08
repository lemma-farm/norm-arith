-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierDefs
public import RothschildStein.G2.ConvolutionSupport
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Set
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

                                                            
                                                                   
                                                                     
                                                               

                                                         
                          
                                                                   
                                                 
                                         
                                        
                                             
        
                                                  
                                                                          
                                                                       

                                                          
                
                                                                     
                                                               
                            
                                                             
                                                              
                                                            

/-- Scaling preserves smoothness (BB p. 121). -/
theorem contDiff_groupMollifierScale (φ : GroupMollifier G ν) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (groupMollifierScale G φ ε) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (G.dilate ε⁻¹) := by
    have h := (dilationLinearMap G ε⁻¹).toContinuousLinearMap.contDiff (n := (⊤ : ℕ∞))
    have he : ⇑((dilationLinearMap G ε⁻¹).toContinuousLinearMap) = G.dilate ε⁻¹ :=
      funext (dilationLinearMap_apply G ε⁻¹)
    rw [he] at h
    exact h
  exact contDiff_const.mul (φ.smooth.comp hd)

                                                               
theorem hasCompactSupport_groupMollifierScale (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) : HasCompactSupport (groupMollifierScale G φ ε) := by
  let e : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) :=
    { toFun := G.dilate ε⁻¹
      invFun := G.dilate ε
      left_inv := by
        intro x
        rw [dilate_dilate, mul_inv_cancel₀ hε.ne', dilate_one]
      right_inv := dilate_inv_dilate G hε.ne'
      continuous_toFun := continuous_dilate G ε⁻¹
      continuous_invFun := continuous_dilate G ε }
  exact (φ.compact.comp_homeomorph e).mul_left

                                                             
                                                                       
                                                            
                                                                                 
                                                  

                                                                
                                                                           
                                                                                     
            
              
                                                                  

end RothschildStein.G2

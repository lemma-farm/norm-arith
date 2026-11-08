-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierPointwise
public import RothschildStein.G2.MollifierIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Set
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

/-- A group mollifier preserves a global pointwise bound
(BB Prop 3.48 proof, p. 122). -/
theorem norm_groupRegularize_le (φ : GroupMollifier G ν) {f : (Fin N → ℝ) → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {ε : ℝ}
    (hε : 0 < ε) (x : Fin N → ℝ) : ‖groupRegularize G φ f ε x‖ ≤ C := by
  have hφ : Integrable φ := φ.smooth.continuous.integrable_of_hasCompactSupport φ.compact
  have hmeas : AEStronglyMeasurable (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) x)) volume :=
    (φ.smooth.continuous.mul (hf.comp ((continuous_mul G).comp
      (((continuous_inv G).comp (continuous_dilate G ε)).prodMk continuous_const)))).aestronglyMeasurable
  have hb (z : Fin N → ℝ) :
      ‖φ z * f (G.mul (G.inv (G.dilate ε z)) x)‖ ≤ φ z * C := by
    rw [norm_mul, Real.norm_of_nonneg (φ.nonneg z)]
    exact mul_le_mul_of_nonneg_left (hC _) (φ.nonneg z)
  have hi : Integrable (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) x)) volume :=
    Integrable.mono' (hφ.mul_const C) hmeas (Filter.Eventually.of_forall fun z =>
      hb z)
  rw [groupRegularize_eq_integral G φ f hε]
  calc
    _ ≤ ∫ z, ‖φ z * f (G.mul (G.inv (G.dilate ε z)) x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, φ z * C := integral_mono hi.norm (hφ.mul_const C) hb
    _ = C := by rw [integral_mul_const, φ.integral_eq_one, one_mul]

                                                         
                                                  
                                                                          
                                                                                     
                                     
                     
         
                                                                                        

                                                               
                                                                     
                                                                              
                                                      
                                                         
                                                                                   
                                                                                   
                                                                                                 
                                                                                      
                                                                     
                    
                                                                               
                                        
              
                                               
                                        
           
            
                                                             
                                                                    
                                        
                                                        

end RothschildStein.G2

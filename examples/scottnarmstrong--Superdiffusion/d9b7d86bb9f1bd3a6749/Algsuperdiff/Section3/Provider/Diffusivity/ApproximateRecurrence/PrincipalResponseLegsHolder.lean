/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Provider: sub-step (iv) of the principal response, the Hoelder leg

Source displays in ABK26:

* The first moment of Step 3's bad-event estimate,

  ```
  E[ | bfAhom_{m-1}^{-1/2} bfA_m(cu_n) bfAhom_{m-1}^{-1/2} |^8 ]^{1/8} <= C gamma^{-1} ,
  ```

* The second moment,

  ```
  ( avsum_{z} E[ | bfAhom_{m-1}^{1/2} P_z |^4 ] )^{1/4} <= C ,
  ```

* The conclusion

  ```
  avsum_z E[ P_z . bfA_m(z+cu_n) P_z 1_{not Q_z} ] <= C gamma^{-2} exp(-gamma^{-1})
                                                  <= (1/2) gamma^6 .
  ```

This module supplies the **Hoelder arithmetic** of that chain and nothing else.
Write `B` for the normalized matrix size of the first display and `V` for the
normalized load length of the second, so that the energy observable obeys the
pointwise domination `X <= B . V^2` used in the conclusion display.  Then the
printed four-way split `1/8 + 1/4 + 1/4 + 3/8 = 1` is realized here as two
nested two-factor Hoelder inequalities: an inner one at the conjugate pair
`(8, 2)` bounding `‖B
V^2‖_{8/5}` by `‖B‖_8 ‖V‖_4^2`, and an outer one at the conjugate pair `(8/5,
8/3)` separating the energy from the indicator of the bad event.

## The tail exponent is `3/8`, not `1`

Every statement below carries the honest exponent `3/8`; the printed exponent
`1` occurs nowhere.

## Main results

* `holderConjugate_eightFifths_eightThirds`, `holderTriple_eight_two_eightFifths`
* `eLpNorm_energy_le_of_moments` -- the inner split's energy factor.
* `integral_rpow_le_of_eLpNorm_le` -- descent from the seminorm to the source's
  own real moment root.
* `integral_mul_indicator_le_of_moment` -- the outer split at the exponent `3/8`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-! ## The two conjugate pairs -/

                                                             
                                                 
                                             
                               
                          

                                                                                  
                                                                 
                                             
                                          
             
                                                  
                                                        
                                                      
                                                      
                                                                       
                                                       
           
          

                                            

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}

                                                                            
                                                   
                                    
                                                  
                                          
                
                                                    
                                                                  
                                                           
                                                         
            
                                                                                           
                          
                                                       
          

                                                                                  
                                                                             
                           

                                                                              
                                                                             
                           
                                                        
                                                             
                                
                                                           
                                                                       
                                               
                                              
                                                
                                                                   
                                                                          
             
                                     
                                                                         
                                       
                                                            
                       
                
                                                                      
                          
                    
                
                                                                     
                                             
                                                             
                                                                                 
                                                   
                 
        
                                     
                                             
                                                                               
                                                           
                                 
                                                  
                                     
                                                           

                                                  

                                                                           
                                                                                
                                                                                
                                       
theorem integral_rpow_le_of_eLpNorm_le {X : Omega → ℝ}
    (hX0 : ∀ omega, 0 ≤ X omega) {p : ℝ} (hp : 0 < p)
    (hmem : MemLp X (ENNReal.ofReal p) mu) {R : ℝ} (hR : 0 ≤ R)
    (h : eLpNorm X (ENNReal.ofReal p) mu ≤ ENNReal.ofReal R) :
    (∫ omega, X omega ^ p ∂mu) ^ (1 / p) ≤ R := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simpa using hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hrepr := hmem.eLpNorm_eq_integral_rpow_norm hp0 hptop
  rw [htoReal] at hrepr
  have hnorm : (fun omega => ‖X omega‖ ^ p) = fun omega => X omega ^ p := by
    funext omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 omega)]
  rw [hnorm] at hrepr
  rw [hrepr] at h
  have hnn : (0 : ℝ) ≤ (∫ omega, X omega ^ p ∂mu) ^ p⁻¹ :=
    Real.rpow_nonneg (integral_nonneg fun omega => Real.rpow_nonneg (hX0 omega) p) _
  have := (ENNReal.ofReal_le_ofReal_iff hR).1 h
  rwa [one_div]

/-! ## The outer split at the exponent `3/8` -/

                                                                                
                                                              

   
                                                       
      
                                                                         
                                                      
                                                                             
                                                                 
                                                          
                                     
                                                   
                                        
                                                           
                                    
                                                     
                                            
                                                         
                                                     
                                                              
                       
                                                            
                                                  
               
                               
                                                     
                                                                       
                                                                                  
                     
                   
                                                   
                       
                                                              
                                                              
                         

                                                                              
                                                        

   
                                     
   
  
                                                                
                                                      
                                                                           
                   
                                                                      
                                                    
                                                                 
                                     
                 
                                                                 
                                                             
                                                            
                                                   
                                         
                                         

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

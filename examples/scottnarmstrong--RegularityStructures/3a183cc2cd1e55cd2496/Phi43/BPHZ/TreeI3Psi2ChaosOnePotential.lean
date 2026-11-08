/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneSplit
public import Phi43.BPHZ.TreeI3PsiLeaves

/-!
# Convolution estimates for the absolute value of the kernel `J`

* `integral_swap_nonneg`: Tonelli for nonnegative functions in terms of Bochner integrals;
* `abs_J_mul_J_le`: `∫ |J(w - y)| |J(w' - y)| dy ≤ C B² s(w - w')^(-1)`;
* `power_mul_abs_J_le`: `∫ s(c - y)^(-a) |J(w - y)| dy ≤ C B s(c - w)^(2-a)` for `a ∈ (2, 5)`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- Tonelli for nonnegative functions: finiteness of one iterated integral gives integrability on
the product and equality of the iterated integrals. -/
theorem integral_swap_nonneg {G : SpaceTime → SpaceTime → ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry G) (volume.prod volume))
    (h0 : ∀ w y, 0 ≤ G w y) (hG : ∀ᵐ w : SpaceTime ∂volume, Integrable (G w))
    (hH : Integrable (fun w => ∫ y, G w y)) :
    Integrable (Function.uncurry G) (volume.prod volume) ∧
      Integrable (fun y => ∫ w, G w y) ∧ ∫ y, ∫ w, G w y = ∫ w, ∫ y, G w y := by
  have hint : Integrable (Function.uncurry G) (volume.prod volume) := by
    refine (integrable_prod_iff hm).2 ⟨hG, ?_⟩
    refine hH.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (h0 _ _)]
  exact ⟨hint, hint.integral_prod_right, (integral_integral_swap hint).symm⟩

                                                        
                                                                                        
                                                            
                                                 

                                                           
                                             
                                                          
                                                                                       
                                                           
                                                          
                                                                                                           
                                                                                   
                                                                         
                                               
                             
                                                                                       
                 
                                                               
                                                                                        
                                                                                      
                                                                   
                                                            
                                                                                                 
                                                                                             
                                                
                                   
        
                                                               
                                  
                                                                                   
            
                                                                                                   
                                                                       
                                                              
                                                                                           
                                                                        
                                                   
                      

                                                              
                                                                                            
                                                          
                                                                                       
                                                         
                                                               
                                                                                                       
                                                                                   
                                                    
                                              
                            
                                                                                                
                                                                    
                                    
                                                                                      
                                                                        
                                                       
                                                              
                                                                                             
                                   
        
                                                               
                                  
                                                                                               
            
                                                                                                   
                                                                       
                                                                          
                                                                                      
                                                               
                                        
                      

end RegularityStructures

end

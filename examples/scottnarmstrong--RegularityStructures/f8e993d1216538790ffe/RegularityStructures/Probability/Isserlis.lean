/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianVector

/-!
# The Isserlis–Wick formula for fourth moments

For a centred Gaussian vector `X` with covariance `C`,

* `E[Xᵢ Xⱼ Xₖ Xₗ] = Cᵢⱼ Cₖₗ + Cᵢₖ Cⱼₗ + Cᵢₗ Cⱼₖ` (`integral_mul_mul_mul`);
* `E[(Xᵢ² - Cᵢᵢ)(Xⱼ² - Cⱼⱼ)] = 2 Cᵢⱼ²` (`integral_sq_sub_mul_sq_sub`), the covariance of Wick
  squares;
* `E[Xᵢ Xⱼ Xₖ] = 0` (`IsCentredGaussianVector.integral_mul_mul_eq_zero`, in
  `RegularityStructures.Probability.GaussianVector`).

## Proof

Polarisation. For `x ∈ ℝ⁴`,
`192 x₀ x₁ x₂ x₃ = ∑_{s ∈ {±1}³} s₁ s₂ s₃ (x₀ + s₁ x₁ + s₂ x₂ + s₃ x₃)⁴`.
Each linear form `L = Xᵢ + s₁ Xⱼ + s₂ Xₖ + s₃ Xₗ` is a centred real Gaussian, so
`E[L⁴] = 3 E[L²]²`, and `E[L²]` is a quadratic form in `C`. Summing the eight identities gives the
formula. The same identity, with integrability of each `L⁴`, shows that `Xᵢ Xⱼ Xₖ Xₗ` is integrable.
-/

public section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

/-! ### Polarisation of the fourth power -/

                         
                                       

                                                                         
                                                               
                                     

                                                 
                                                                      
                                       

                                                   
                                                                                  
                                                                                             
      

                                                                                            
             
                                   
                                                                           
                                                  

namespace IsCentredGaussianVector

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

                                                                        
                                                                                      
                                                               
                        
                                                                                        
                                               
                                                                                    
                                                                               

                                                                                 
                                                  
                                                                                    
                                                                                               
                                        
                                     
                                                                                   
                                                          
                                                                                             
                                                                             
      

                                                                            
                                                                                      
                                                                           
                                
                                                             
                                                                                         
                           
           
        
               
                                             
                                                     
                                                     
                                                                                              
             
                                                                                          
                                             
                                                                                   
                                                                                                   
      
      

                                                                     
theorem integrable_sq_sub_mul_sq_sub (h : IsCentredGaussianVector P X C) (i j : Fin n)
    (a b : ℝ) :
    Integrable (fun ω => (X ω i ^ 2 - a) * (X ω j ^ 2 - b)) P := by
  have := h.isProbabilityMeasure
  have e : (fun ω => (X ω i ^ 2 - a) * (X ω j ^ 2 - b)) =
      fun ω => X ω i ^ 2 * X ω j ^ 2 - b * X ω i ^ 2 - a * X ω j ^ 2 + a * b := by
    funext ω
    ring
  rw [e]
  exact (((h.integrable_pow_mul_pow i j 2 2).sub ((h.integrable_pow_apply i 2).const_mul b)).sub
    ((h.integrable_pow_apply j 2).const_mul a)).add (integrable_const _)

end IsCentredGaussianVector

end RegularityStructures

end

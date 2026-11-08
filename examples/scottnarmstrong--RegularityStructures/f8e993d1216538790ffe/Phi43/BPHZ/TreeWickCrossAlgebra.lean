/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Second differences of powers of the cross covariances

With `a = Q_{εε}`, `b = Q_{εε'}`, `c = Q_{ε'ε}`, `d = Q_{ε'ε'}` and
`σ = a + b + c + d`, `r = a - b - c + d`, `e₁ = a + b - c - d`, `e₂ = a - b + c - d` one has the
exact identities
`a² - b² - c² + d² = (r σ + e₁ e₂) / 2` and
`a³ - b³ - c³ + d³ = (3 (e₁² r + e₂² r + 2 e₁ e₂ σ + σ² r) + r³) / 16`.
Since `|σ|, |r|, |eᵢ| ≲ s⁻¹`, `|r| ≲ (max ε ε')^(2θ) s^(-1-2θ)` and
`|eᵢ| ≲ (max ε ε')^θ s^(-1-θ)`, this gives `(max ε ε')^(2θ)` smallness of both second differences
with the full singularity `s⁻²` (respectively `s⁻³`) of the undifferenced quantity, up to `s^(-2θ)`.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

                                                                                          
                                                
                       
                                            
                                                                                         

                                                                                         
                                                            
                                                                 
                                                                                       

theorem treeWick_alg_sq {σ r e₁ e₂ A μ p q : ℝ} (hA : 0 ≤ A) (hμ : 0 ≤ μ) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hσ : |σ| ≤ A * p) (hr : |r| ≤ A * (μ ^ 2 * p * q ^ 2))
    (h₁ : |e₁| ≤ A * (μ * p * q)) (h₂ : |e₂| ≤ A * (μ * p * q)) :
    |(r * σ + e₁ * e₂) / 2| ≤ A ^ 2 * (μ ^ 2 * p ^ 2 * q ^ 2) := by
  have t1 : |r * σ| ≤ A * (μ ^ 2 * p * q ^ 2) * (A * p) := by
    rw [abs_mul]
    exact mul_le_mul hr hσ (abs_nonneg _) (by positivity)
  have t2 : |e₁ * e₂| ≤ A * (μ * p * q) * (A * (μ * p * q)) := by
    rw [abs_mul]
    exact mul_le_mul h₁ h₂ (abs_nonneg _) (by positivity)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
  calc |r * σ + e₁ * e₂| ≤ |r * σ| + |e₁ * e₂| := abs_add_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring

                                                                                        
                                                                                            
                                                                          
                                    
                                                                                    
                                           
                                       
                                                           
                                                                                    
                    
                                           
                                                                              
                
                                                               
                                                                              
                
                                                               
                                                                              
                                          
                                                                             
                
                                                                 
                                                                         
                                   
                                                                                              
                                                                                  
                                                                              
                                                                                           
                                                            
                                                            
                                                         
                                                        
                                                                    
                                                            
                                                         
                                                                 
                                                          
                                                             
              
                    

end RegularityStructures.Phi43

end

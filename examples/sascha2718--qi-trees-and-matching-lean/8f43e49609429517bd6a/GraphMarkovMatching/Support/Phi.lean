module

/-
The weight `φ_α t = t / (1-t)^α` at a *free* exponent `α`, together with the
elementary facts the support layer needs:

* `le_phi`              `t ≤ φ_α t` on `[0,1)`
* `one_sub_rpow_le`     the tangent line to `t ↦ t^α` at `t = 1` (Bernoulli)
* `rpow_neg_alpha_le`   `(1-t)^{-α} ≤ 1 + α φ_α(t)`
* `chord`               `(1-z)^{-α} ≤ 1 + c_α z` on `[0,1/2]`, `c_α = 2(2^α - 1)`
* `add_sq_le_weighted`  the weighted mean inequality behind `A_δ`

The exponent is a variable throughout.  The chord is proved from concavity
of `log` (both endpoint values of `z ↦ log(1+c_α z) + α log(1-z)` on
`[0,1/2]` vanish), which works for every `α ≥ 0`.
-/
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic

@[expose] public section

namespace GraphMarkovMatching.Support

open Real

/-- `φ_α t = t / (1-t)^α`. The paper defines it on `[0,1)`; off that range
Lean's junk values apply and every lemma below carries `t < 1`. -/
noncomputable def phi (α t : ℝ) : ℝ := t / (1 - t) ^ α

/-- On `(-∞,1)` the denominator of `φ_α` is positive. -/
lemma rpow_denom_pos (α : ℝ) {t : ℝ} (h : t < 1) : 0 < (1 - t) ^ α :=
  Real.rpow_pos_of_pos (by linarith) α

lemma phi_nonneg {α t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : 0 ≤ phi α t :=
  div_nonneg h0 (rpow_denom_pos α h1).le

/-- `t ≤ φ_α t` on `[0,1)`, since `(1-t)^α ≤ 1` for `α ≥ 0`. -/
lemma le_phi {α t : ℝ} (hα : 0 ≤ α) (h0 : 0 ≤ t) (h1 : t < 1) : t ≤ phi α t := by
  rw [phi, le_div_iff₀ (rpow_denom_pos α h1)]
  have h : (1 - t) ^ α ≤ 1 :=
    Real.rpow_le_one (by linarith) (by linarith) hα
  nlinarith

/-- The tangent line to `t ↦ t^α` at `t = 1` lies below the graph:
`1 - r^α ≤ α (1-r)` for `0 ≤ r` and `α ≥ 1` (Bernoulli). -/
lemma one_sub_rpow_le {α r : ℝ} (hα : 1 ≤ α) (hr : 0 ≤ r) :
    1 - r ^ α ≤ α * (1 - r) := by
  have h := one_add_mul_self_le_rpow_one_add (s := r - 1) (by linarith) hα
  have e : (1 : ℝ) + (r - 1) = r := by ring
  rw [e] at h
  linarith

/-- `(1-t)^{-α} ≤ 1 + α φ_α(t)` on `(-∞,1)` for `α ≥ 1`: the form in which
the tangent bound is consumed by the product lemma and the second term of the
contraction lemma (`W(x) - 1 ≤ α φ_α(q(x))`). -/
lemma rpow_neg_alpha_le {α t : ℝ} (hα : 1 ≤ α) (h1 : t < 1) :
    (1 - t) ^ (-α) ≤ 1 + α * phi α t := by
  have hr : (0 : ℝ) < 1 - t := by linarith
  have hp : (0 : ℝ) < (1 - t) ^ α := rpow_denom_pos α h1
  rw [Real.rpow_neg hr.le, inv_eq_one_div, div_le_iff₀ hp]
  have h := one_sub_rpow_le hα hr.le
  have hphi : α * phi α t * (1 - t) ^ α = α * t := by
    rw [phi]; field_simp
  nlinarith [h, hphi]

/-! ### The chord bound at a free exponent

`(1-z)^{-α} ≤ 1 + c_α z` on `[0,1/2]` with the exact chord slope
`c_α = 2(2^α - 1)` through `(0,1)` and `(1/2, 2^α)`. At a free exponent the
proof uses concavity of `log`: the
function `g z = log(1 + c_α z) + α log(1-z)` satisfies `g 0 = g (1/2) = 0`
and is concave, hence nonnegative on `[0,1/2]`, and `exp g` is the claim. -/

                                          
                                                                 

                                                                        
                                                             
                                                                   

                                                                     
                            
                           

                                               
                                         
                                                                      
                                                  
                                                       
                                           
                                                 
                                                
            
                                                            
                                                        
                                     
                                              
                                          
                                               
                                                                
                                                     
                                                                            
                                                                          
                                                                  
                                     
                                  
                                                                                   
                         
                                                                             
                     
                              
                                       
                    
                                                             
                                                         
                                                                        
                                                                
                                     
                                  
                                                                       
                                                           
                     
                              
                                                         
                                
                       
                    
                                         
                                                                   
                                    
                                                                              
                         
                 
                                                   
                                                                               
                                                                             
            
                                                 
                                                                          
                              

                                                                           
                                                                  
                                               
                                          
                                                             
                                                       
                          

                                    

                                                                        
                                                                  
                                                                             
                                                   
                                                           
                                                   
                                                                    
                                                          
                                                                             
                  
                                     
                                                                             
                                                                                   
                             
                                     
          

end GraphMarkovMatching.Support

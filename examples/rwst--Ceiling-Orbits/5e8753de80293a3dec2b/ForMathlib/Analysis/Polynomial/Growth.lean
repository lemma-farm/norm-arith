/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Polynomial growth against geometric decay

Three elementary facts about a real polynomial sampled along `ℕ`, none of which is currently in
Mathlib, all in the neighbourhood of `Mathlib/Analysis/Polynomial/Basic.lean`:

* an explicit majorant `|p(t)| ≤ ‖coeffs‖₁ · t^deg` valid on `[1, ∞)`;
* `|p(n)| · rⁿ → 0` for `0 ≤ r < 1` — geometric decay beats polynomial growth;
* the rigidity consequence: a polynomial whose values along `ℕ` tend to `0` is the zero
  polynomial.

The last one is the useful one.  Mathlib has `Polynomial.abs_tendsto_atTop` (values of a
positive-degree polynomial blow up) but nothing that turns "the values are small" back into a
statement about the polynomial, which is what one needs to rule out a hypothetical recurrence:
derive a bound `|p(n)| ≤ C(n)·rⁿ` with `C` of polynomial growth, conclude `p = 0`, contradiction.

Everything is stated over `ℝ`, matching `tendsto_pow_const_mul_const_pow_of_abs_lt_one`; the
`Mathlib` file these belong next to is stated for a normed linearly ordered field, and the first
lemma generalises verbatim, but the other two use `ℕ`-indexed sampling and are not needed at that
generality here.

## Main results

* `Polynomial.abs_eval_le_of_one_le` — `|p(t)| ≤ (∑ᵢ |pᵢ|) · t^{deg p}` for `1 ≤ t`.
* `Polynomial.tendsto_abs_eval_mul_pow` — `|p(n)| · rⁿ → 0` for `0 ≤ r < 1`.
* `Polynomial.eq_zero_of_tendsto_eval_natCast` — `p(n) → 0` along `ℕ` implies `p = 0`.
-/

namespace Polynomial

open Filter Topology

/-- On `[1, ∞)` a real polynomial is dominated by its degree-power, with the `ℓ¹`-norm of its
coefficients as the constant. -/
lemma abs_eval_le_of_one_le (p : Polynomial ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |p.eval t| ≤ (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * t ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [abs_mul, abs_pow, abs_of_nonneg (by linarith : (0:ℝ) ≤ t)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hi') (abs_nonneg _)

                                                                                  
                                                                                       
                                                                     
                                    
                                                                                            
                       
                                                                       
                                           
                                                                               
                                                                             
                                                  
                                                      
                               
                                                                                                
                                                                                
                                                                                                   
            

                                                                                

                                                                                                
                                                   
                                                        
                                                                         
                                 
                                                           
                                      
                                                   
                               
                                                                          
                                                                    
                                                                 
                                                                                         
                                                          

end Polynomial

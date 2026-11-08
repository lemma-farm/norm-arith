module

/-
Copyright (c) 2026 Logan Kleinwaks. All rights reserved.
Released under Apache 2.0 license; see LICENSE-Kleinwaks.
Reused from kleinwaks/masked-digit-sum-difference-bound,
commit 352ab86effecb7efce415507a8c781ec158b86e0.
-/
/- Modified by Carson Olafson with GPT-6 Astra: ported module visibility
for Lean 4.35.0-rc2; mathematical declarations and proofs are unchanged. -/
public import Mathlib

@[expose] public section

/-!
# Product weights on words and a Chebyshev estimate

This file develops the elementary discrete probability needed for the construction proofs of
`masked_digit_bound.tex`.  In the source the counting is carried out with the method of types
and the multinomial estimate (5) (`eq:multinomial-estimate`); here the equivalent
concentration input is packaged as a second-moment (Chebyshev) estimate for the product
measure `w ↦ ∏ⱼ p (w j)` on words, which is the same Gibbs measure `p` of equation (7)
(`eq:gibbs`) of the source.

The main results are:

* `ProductWeights.sum_wt`: the product weights sum to one;
* `ProductWeights.sum_wt_sq_of_centered`: the exact second moment of a centred additive
  statistic;
* `ProductWeights.mass_deviation_le`: the Chebyshev bound for such a statistic.
-/

open scoped BigOperators

namespace MaskedDigit
namespace ProductWeights

variable {A : Type*} [Fintype A]

/-- The product weight `∏ⱼ p (w j)` of a word `w`, i.e. the Gibbs product measure used in the
construction proofs of `masked_digit_bound.tex`. -/
def wt (p : A → ℝ) {l : ℕ} (w : Fin l → A) : ℝ := ∏ j, p (w j)

                   
                                                                                         
                                    

                                                                                                                                                                          
                                                          
                                     
                                                                  
                             

                                                                             
theorem sum_wt_single (p : A → ℝ) (hsum : ∑ a, p a = 1) (g : A → ℝ) {l : ℕ} (j₀ : Fin l) :
    ∑ w : Fin l → A, wt p w * g (w j₀) = ∑ a, p a * g a := by
  classical
  set F : Fin l → A → ℝ := fun j a => p a * (if j = j₀ then g a else 1) with hF
  have hprod : ∀ w : Fin l → A, ∏ j, F j (w j) = wt p w * g (w j₀) := by
    intro w
    simp only [hF, wt, Finset.prod_mul_distrib]
    congr 1
    simp
  have hsumF : ∀ j : Fin l, ∑ a, F j a = (if j = j₀ then (∑ a, p a * g a) else 1) := by
    intro j
    by_cases h : j = j₀ <;> simp [hF, h, hsum]
  calc ∑ w : Fin l → A, wt p w * g (w j₀)
      = ∑ w : Fin l → A, ∏ j, F j (w j) := (Finset.sum_congr rfl fun w _ => (hprod w).symm)
    _ = ∏ j, ∑ a, F j a := (Fintype.prod_sum F).symm
    _ = ∑ a, p a * g a := by simp [hsumF]

/-- Expectation of a product of two distinct coordinates under the product weights. -/
theorem sum_wt_pair (p : A → ℝ) (hsum : ∑ a, p a = 1) (g h : A → ℝ) {l : ℕ} {j₀ j₁ : Fin l}
    (hne : j₀ ≠ j₁) :
    ∑ w : Fin l → A, wt p w * (g (w j₀) * h (w j₁)) =
      (∑ a, p a * g a) * (∑ a, p a * h a) := by
  classical
  set F : Fin l → A → ℝ :=
    fun j a => p a * (if j = j₀ then g a else 1) * (if j = j₁ then h a else 1) with hF
  have hprod : ∀ w : Fin l → A, ∏ j, F j (w j) = wt p w * (g (w j₀) * h (w j₁)) := by
    intro w
    simp only [hF, wt, Finset.prod_mul_distrib]
    rw [Finset.prod_ite_eq' Finset.univ j₀ (fun j => g (w j)),
      Finset.prod_ite_eq' Finset.univ j₁ (fun j => h (w j))]
    simp [mul_assoc]
  have hsumF : ∀ j : Fin l, ∑ a, F j a =
      (if j = j₀ then (∑ a, p a * g a) else 1) * (if j = j₁ then (∑ a, p a * h a) else 1) := by
    intro j
    simp only [hF]
    by_cases h0 : j = j₀
    · simp [h0, hne]
    · by_cases h1 : j = j₁ <;> simp [h0, h1, hsum, Ne.symm hne]
  calc ∑ w : Fin l → A, wt p w * (g (w j₀) * h (w j₁))
      = ∑ w : Fin l → A, ∏ j, F j (w j) := (Finset.sum_congr rfl fun w _ => (hprod w).symm)
    _ = ∏ j, ∑ a, F j a := (Fintype.prod_sum F).symm
    _ = (∑ a, p a * g a) * (∑ a, p a * h a) := by
        rw [Finset.prod_congr rfl (fun j _ => hsumF j), Finset.prod_mul_distrib,
          Finset.prod_ite_eq' Finset.univ j₀ (fun _ => (∑ a, p a * g a)),
          Finset.prod_ite_eq' Finset.univ j₁ (fun _ => (∑ a, p a * h a))]
        simp

/-- **Exact second moment of a centred additive statistic.**  If `∑ₐ p a * g a = 0`, then the
statistic `w ↦ ∑ⱼ g (w j)` has second moment `l * ∑ₐ p a * g a ^ 2` under the product weights.
This replaces the variance computation implicit in the concentration step of the proofs of
Propositions 2 and 4 of `masked_digit_bound.tex`. -/
theorem sum_wt_sq_of_centered (p : A → ℝ) (hsum : ∑ a, p a = 1) (g : A → ℝ)
    (hg : ∑ a, p a * g a = 0) (l : ℕ) :
    ∑ w : Fin l → A, wt p w * (∑ j, g (w j)) ^ 2 = l * ∑ a, p a * g a ^ 2 := by
  classical
  have expand : ∀ w : Fin l → A, (∑ j, g (w j)) ^ 2 = ∑ j, ∑ j', g (w j) * g (w j') := by
    intro w
    rw [sq, Finset.sum_mul_sum]
  have step1 : ∑ w : Fin l → A, wt p w * (∑ j, g (w j)) ^ 2
      = ∑ w : Fin l → A, ∑ j : Fin l, ∑ j' : Fin l, wt p w * (g (w j) * g (w j')) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [expand w, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
  have step2 : ∑ w : Fin l → A, ∑ j : Fin l, ∑ j' : Fin l, wt p w * (g (w j) * g (w j'))
      = ∑ j : Fin l, ∑ j' : Fin l, ∑ w : Fin l → A, wt p w * (g (w j) * g (w j')) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [step1, step2]
  have step3 : ∀ j j' : Fin l, ∑ w : Fin l → A, wt p w * (g (w j) * g (w j'))
      = (if j = j' then (∑ a, p a * g a ^ 2) else 0) := by
    intro j j'
    by_cases hjj : j = j'
    · subst hjj
      rw [if_pos rfl]
      have := sum_wt_single p hsum (fun a => g a * g a) j
      simpa [sq] using this
    · rw [if_neg hjj, sum_wt_pair p hsum g g hjj, hg]
      ring
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => step3 j j'))]
  simp [Finset.sum_ite_eq]

                                                                                         
                                                                                           
                                                                        
                            
                                                                                           
                                                            
                                                                                
                                            
           
                                                                                   
                                                                                           
                       
                                  
                                                      
                                                 
                                             
                                                         
                                    
                                                     
                                                                        
                                
                                                  
                                                            
                                                                                    
                     
                                                         
                                                 
                                  
                

                           

section Gibbs

                     

                                                                              
                            
                                                                                          

                                                                                           
                                                                                        
                                                               

                                                                                     
                                                                                        
                                                                               

                                                                                   
          
                                                                                     
                                     
                                                         

                    
                                                                                           
                                                                                    
                                                                 
                                                                             
                                                                                     
                                                 

end Gibbs

end ProductWeights
end MaskedDigit

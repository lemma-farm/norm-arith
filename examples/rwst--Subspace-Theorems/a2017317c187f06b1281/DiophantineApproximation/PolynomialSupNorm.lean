/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Polynomial.Norm

-- Used only inside proofs and in the acceptance criteria.
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# The naive height of an integer polynomial

The **naive height** of `P = ∑ aᵢ Xⁱ` is `max |aᵢ|`, and it is the height that Mahler's and
Koksma's exponents are normalized by. Mathlib already has it, under a name that says what it is
rather than what it is used for: `Polynomial.supNorm`, the Gauss norm of the norm of the
coefficient ring at `c = 1`. Nothing is redefined here. What is missing is the API that Layer 1.2
runs on, and it is of two kinds.

The first is arithmetic, and holds over any seminormed ring: subadditivity, the behaviour under
multiplication by a constant, and the invariance under `Polynomial.reflect`, which reverses the
coefficients and so permutes the very set the supremum is taken over.

The second is **Northcott's theorem for integer polynomials**, and it is the reason the exponents
of Layer 1.2 can be defined by an infinite set of solutions and used through a bound on the
height: over `ℤ` a polynomial of bounded degree and bounded naive height lies in a finite set, so
an infinite set of solutions of bounded degree has *unbounded* height, and any constant in front
of `H(P) ^ (-w)` can be absorbed by lowering `w`. Over `ℚ` this fails — `C (1 / n)` has height
`1 / n` — and the failure is exactly the integrality that makes `1 ≤ H(P)` for `P ≠ 0`.

## Main results

* `Polynomial.supNorm_add_le`, `Polynomial.supNorm_sum_le`, `Polynomial.supNorm_C_mul`,
  `Polynomial.supNorm_le_of_forall` and `Polynomial.supNorm_reflect`: the arithmetic of the naive
  height over a seminormed ring. Reflection, which reverses the coefficients, preserves it
  *exactly*.
* `Polynomial.supNorm_linear` and `Polynomial.coeff_linear_zero`, `_one`, `_add_two`: the naive
  height of `a X + b` is `max |a| |b|` — the naive height of the fraction `-b / a` in the sense
  of Layer 1.1.
* `Polynomial.one_le_supNorm` and `Polynomial.supNorm_pos`: over `ℤ`, a nonzero polynomial has
  height at least `1`.
* `Polynomial.finite_setOf_natDegree_le_supNorm_le`: **Northcott for integer polynomials**, the
  finiteness of the polynomials of bounded degree and bounded naive height.
* `Polynomial.infinite_sep_lt_supNorm`: an infinite set of integer polynomials of bounded degree
  still has infinitely many members above any given height, and
  `Polynomial.infinite_of_forall_exists_lt_supNorm`, the converse direction.
* `Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt` and
  `Polynomial.exists_pos_lt_supNorm_of_abs_sub_root_lt`: **the two height gaps**. Below a
  threshold that depends only on the height bound, a nonzero value at `ξ` — respectively a root
  at positive distance less than the threshold from `ξ` — forces the naive height above that
  bound. Layer 1.2 uses one or the other every time it replaces a solution by another polynomial.
* `Polynomial.supNorm_comp_le` and `Polynomial.one_le_sum_supNorm_pow`: a substitution multiplies
  the naive height by at most a constant depending only on the substituted polynomial and the
  degree bound.

## Implementation notes

⚠ **`Polynomial.supNorm` is the naive height and no wrapper is introduced.** Mathlib's own
module documentation says so ("often called the *(naive) height*") and declines the name because
`Height` is taken; a local abbreviation would only hide `Polynomial.le_supNorm` and
`Polynomial.exists_eq_supNorm`, which are what every proof below uses. The zero polynomial has
height `0`, not the junk value `1` of the projective heights — `supNorm` is a norm, not a height —
and every statement of Layer 1.2 excludes it through `0 < |P ξ|` anyway.

The finiteness proof reads a polynomial of degree at most `n` off its coefficient vector on
`Fin (n + 1)`; that map is injective there, and its image lands in a product of finite intervals
of `ℤ`. The bound on a coefficient is `⌈B⌉`, so the statement is for a real bound and no
integrality of `B` is assumed.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), §3.1. E.
Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.6.

This is part of Layer 1.2 of the `DiophantineApproximation` roadmap.
-/

public section

namespace Polynomial

/-! ### The naive height over a seminormed ring -/

section Seminormed

variable {A : Type*} [SeminormedRing A]

                                                                                   
                                             
                    
                                                                              

theorem supNorm_le_of_forall {P : A[X]} {c : ℝ} (h : ∀ i, ‖P.coeff i‖ ≤ c) : P.supNorm ≤ c := by
  obtain ⟨i, hi⟩ := P.exists_eq_supNorm
  rw [hi]
  exact h i

                                                                  
                                                         
           
                                              
                 
                     
                                           
                                                  

                                                                                               
                                  
                                                           
                                             
                          
                                                 
                                  
                                                                    
                                         
                                      
                        

/-- Reversing the coefficients of a polynomial does not change its naive height: `revAt N` is an
involution of `ℕ`, so it permutes the family the supremum is taken over. -/
theorem supNorm_reflect (N : ℕ) (P : A[X]) : (P.reflect N).supNorm = P.supNorm := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := (P.reflect N).exists_eq_supNorm
    rw [hi, coeff_reflect]
    exact P.le_supNorm _
  · obtain ⟨i, hi⟩ := P.exists_eq_supNorm
    have hc : (P.reflect N).coeff (revAt N i) = P.coeff i := by
      rw [coeff_reflect, revAt_invol]
    rw [hi, ← hc]
    exact (P.reflect N).le_supNorm _

end Seminormed

/-! ### Integrality and Northcott -/

section Integer

variable {P : ℤ[X]}

theorem abs_coeff_le_supNorm (P : ℤ[X]) (i : ℕ) : |((P.coeff i : ℤ) : ℝ)| ≤ P.supNorm := by
  simpa [Int.norm_eq_abs] using P.le_supNorm i

                                                                                            
                                                                                     
                                                                   
                                                         
                                                                    
                                                 
                                        
                                     
                                 

                                                   
                                          

theorem coeff_linear_zero {R : Type*} [Semiring R] (a b : R) :
    (C a * X + C b).coeff 0 = b := by
  rw [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, coeff_C_zero, zero_add]

theorem coeff_linear_one {R : Type*} [Semiring R] (a b : R) :
    (C a * X + C b).coeff 1 = a := by
  rw [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C_of_ne_zero one_ne_zero, add_zero]

theorem coeff_linear_add_two {R : Type*} [Semiring R] (a b : R) (i : ℕ) :
    (C a * X + C b).coeff (i + 2) = 0 := by
  rw [coeff_add, coeff_C_mul, coeff_X_of_ne_one (by omega), mul_zero,
    coeff_C_of_ne_zero (by omega), add_zero]

/-- The naive height of a linear integer polynomial is the larger of the two coefficients. This
is the naive height of the fraction `-b / a` in the sense of Layer 1.1. -/
theorem supNorm_linear (a b : ℤ) :
    (C a * X + C b).supNorm = max |(a : ℝ)| |(b : ℝ)| := by
  have h0 := coeff_linear_zero a b
  have h1 := coeff_linear_one a b
  have hn := coeff_linear_add_two a b
  refine le_antisymm ?_ (max_le ?_ ?_)
  · obtain ⟨i, hi⟩ := (C a * X + C b : ℤ[X]).exists_eq_supNorm
    rw [hi]
    rcases i with _ | _ | i
    · rw [h0, Int.norm_eq_abs]; exact le_max_right _ _
    · rw [h1, Int.norm_eq_abs]; exact le_max_left _ _
    · rw [hn i, norm_zero]; positivity
  · have h := (C a * X + C b : ℤ[X]).le_supNorm 1
    rwa [h1, Int.norm_eq_abs] at h
  · have h := (C a * X + C b : ℤ[X]).le_supNorm 0
    rwa [h0, Int.norm_eq_abs] at h

                                                                                            
                                        
                                                              
                                                             
           
                                                                                               
                            
                                                                        
                                   
                                                    
                                                                  
                             
                                                             
                                                
                                  
         
                                    
                                                  
                                                         
                                                       

                                                                                                
                                                                                      
                  
                                                   
                                                         
                                            
                                             
           
                                                               
                                         

                                                                                                  
                                                                                               
                                             
                                                                     
                                                                                        
           
                                               
                                                         
             
                                                
                   
                                                                           
                                                                        
                                      
                         
                                                                         
                              
                  
                                 
                                                                                         
                                                                                
                                                                             
                                                                  
                                   
                                                                                  
                                                                       
                                       

                                                                    
                                         
                                                          
                                       

                                                                                                
                                                                                                
                                                   
                                                                        
                                                                                      
                                               
                                                                                    
                                                          
                                               

                                                                                                
                                                                                                  
                                                                                                
                                                                                           
                                                                                           
                                                                                    
                                                                       
                                                                                      
                         
           
                                                                                     
                                                                                            
                                                                                        
                         
                  
                                                                              
                                               
                                                                                          
                                                                                      
                                                                                               
                                            

                                                                                          
                                                                                            
                                                                                            
                                                                                                 
                                                                                           
                                                                                           
                                                                          
                                                                                    
                                                     
           
                                                                        
              
                                             
                                                                       
                                                                                           
           
                                                   
             
                                      
                  
                                                                                           
           
                             
                                                
                                                                                               
                      
                                       
            
                                                
                                            
                                                                                           
                   
                                                                                              
                                                                     
                                         
                  
                                                                        
                                                                          
                                          
                                               
                                                                                 
                                                                                  
                                     
                                                         

                                                           
                                                            
            
                                                    
                             
                                        

end Integer

end Polynomial

/-! ### Acceptance criteria -/

section Examples

open Polynomial

/-- The naive height is the largest absolute value of a coefficient. -/
example : (X - C 2 : ℤ[X]).supNorm = 2 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := (X - C 2 : ℤ[X]).exists_eq_supNorm
    rw [hi]
    rcases i with _ | _ | i <;> simp [coeff_X, Int.norm_eq_abs]
  · have h0 : ((X - C 2 : ℤ[X]).coeff 0) = -2 := by simp
    have h := (X - C 2 : ℤ[X]).le_supNorm 0
    rw [h0, Int.norm_eq_abs] at h
    norm_num at h
    exact h

/-- Reversing the coefficients permutes them, so it leaves the naive height alone. -/
example (P : ℤ[X]) : (P.reflect 7).supNorm = P.supNorm := supNorm_reflect 7 P

/-- **Rejection test: integrality is what makes `1 ≤ H(P)`.** Over `ℚ` the naive height of a
nonzero polynomial can be as small as one likes, and with it the whole absorption argument of
Layer 1.2 collapses. -/
example : ¬ ∀ P : ℚ[X], P ≠ 0 → 1 ≤ P.supNorm := by
  intro h
  have h1 := h (C (1 / 2 : ℚ)) (by simp)
  rw [supNorm_C, ← Rat.norm_cast_real, Real.norm_eq_abs] at h1
  norm_num at h1

/-- **Rejection test: the degree bound in Northcott is load-bearing.** The powers of `X` all have
naive height `1`, so bounding the height alone leaves an infinite set. -/
example : ¬ {P : ℤ[X] | P.supNorm ≤ 1}.Finite := by
  intro h
  have hsub : Set.range (fun k : ℕ ↦ (X : ℤ[X]) ^ k) ⊆ {P : ℤ[X] | P.supNorm ≤ 1} := by
    rintro P ⟨k, rfl⟩
    change ((X : ℤ[X]) ^ k).supNorm ≤ 1
    rw [← monomial_one_right_eq_X_pow, supNorm_monomial]
    simp
  refine Set.infinite_range_of_injective (fun k l hkl ↦ ?_) (h.subset hsub)
  simpa using congrArg Polynomial.natDegree hkl

end Examples

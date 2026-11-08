/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Bounds.Defs

/-!
# Stammering sequences

**Layer 7.4, the words** (Adamczewski–Bugeaud–Luca 2004; Adamczewski–Bugeaud 2007, §4). For a
finite word `V` and real `w ≥ 1`, the word `V ^ w` is `V` repeated `⌊w⌋` times followed by the
prefix of `V` of length `⌈(w - ⌊w⌋) |V|⌉`. A sequence `a` is **stammering** if for some `w > 1`
there are finite words `U k`, `V k` with `U k (V k) ^ w` a prefix of `a`, `|U k| / |V k|` bounded
and `|V k|` strictly increasing. This file states the definitions and converts them into the
statement about periods that the transcendence proofs use.

## Main definitions

* `List.rpow`: `V ^ w` for a finite word `V` and real `w`.
* `Function.IsEventuallyPeriodic`: a sequence with a period from some index on.
* `Function.IsStammeringWith`: Condition `(∗)_w`.
* `Function.IsStammering`: Condition `(∗)_w` for some `w > 1`.

## Main results

* `List.length_rpow`: `|V ^ w| = ⌈w |V|⌉`.
* `List.rpow_prefix_append`: `V ^ w` is a prefix of `V ++ V ^ w`.
* `List.getElem?_rpow`: the `j`-th letter of `V ^ w` is the `(j mod |V|)`-th letter of `V`.
* `Function.IsStammeringWith.exists_periodic`: the segment of `a` of length `⌈w |V k|⌉` after
  position `|U k|` has period `|V k|`.
* `Function.isStammeringWith_of_periodic`: the converse.

## Implementation notes

⚠ **Only the lengths survive.** Once `U k (V k) ^ w` is known to be a prefix of `a`, the words are
determined by their lengths and by `a`; everything the transcendence criteria use is the pair
`r k = |U k|`, `s k = |V k|` and the periodicity of `a` on `[r k, r k + ⌈w s k⌉)`. That is
`IsStammeringWith.exists_periodic`, and it is the shape of Condition `(∗)_w` in which the
criterion is proved.

⚠ **The fractional power has the expected length, and no more.** `⌈(w - ⌊w⌋) |V|⌉ ≤ |V|` because
`w - ⌊w⌋ < 1`, so the `List.take` never runs out and `|V ^ w| = ⌊w⌋ |V| + ⌈(w - ⌊w⌋) |V|⌉ =
⌈w |V|⌉`.

## References

B. Adamczewski, Y. Bugeaud and F. Luca, *Sur la complexité des nombres algébriques*, C. R. Acad.
Sci. Paris **339** (2004), 11–14; B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic
numbers I. Expansions in integer bases*, Annals of Mathematics **165** (2007), 547–565.

This is part of Layer 7.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

namespace List

variable {α : Type*}

/-- **The `w`-th power of a finite word**, for real `w ≥ 0`: `V` repeated `⌊w⌋` times, followed
by the prefix of `V` of length `⌈(w - ⌊w⌋) |V|⌉`. Its length is `⌈w |V|⌉`
(`List.length_rpow`). -/
noncomputable def rpow (V : List α) (w : ℝ) : List α :=
  (replicate ⌊w⌋₊ V).flatten ++ V.take ⌈(w - ⌊w⌋₊) * V.length⌉₊

/-- The length of `V ^ w` is `⌈w |V|⌉`: the fractional part of `w` never asks for more than one
copy of `V`. -/
theorem length_rpow (V : List α) {w : ℝ} (hw : 0 ≤ w) :
    (V.rpow w).length = ⌈w * V.length⌉₊ := by
  have hfrac : w - ⌊w⌋₊ < 1 := by linarith [Nat.lt_floor_add_one w]
  have hfrac0 : 0 ≤ w - ⌊w⌋₊ := by linarith [Nat.floor_le hw]
  have hle : ⌈(w - ⌊w⌋₊) * V.length⌉₊ ≤ V.length :=
    Nat.ceil_le.mpr (by nlinarith [(Nat.cast_nonneg V.length : (0 : ℝ) ≤ V.length)])
  have hsplit : w * V.length = (w - ⌊w⌋₊) * V.length + ((⌊w⌋₊ * V.length : ℕ) : ℝ) := by
    push_cast; ring
  rw [rpow, length_append, length_take, min_eq_left hle, hsplit,
    Nat.ceil_add_natCast (mul_nonneg hfrac0 (Nat.cast_nonneg _))]
  simp [length_flatten, add_comm]

                                                                                                
                                                                                  
                                                                                      
                                                                                             
                                                
                                                                                      

                                                                                           
                                            
                                                                    
         
                                                
             
            
                                            
                                                          
                                        
                                 
                                                   
                                          
                         
               
             
                               
                                                         
                     
                                                                             
                               

end List

namespace Function

variable {α : Type*}

/-- A sequence is **eventually periodic** if it has a period `p > 0` from some index `N` on. -/
def IsEventuallyPeriodic (a : ℕ → α) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → a (n + p) = a n

                                                                                             
                                                                                           
              
                                                  
                     
                                                                                        
                                                                    
                                   

                                                                                       
                                                                            

                                                                                                 
                                                                                                 
                                                                                  
                     
                                                                         
                                
                                                                   
                                  
                                                                           
                                          
                                                                                            
                                                                                            
                                                            
                                                                
                                                
                                                                            
                              
                             
                                                                       
                           
                           
                       
                       
                      
                                                                     
                                                                     
                                                            
                                                                                    
                                                       
                                                                
                                             
                        
                                                                                         
                                               
                                              
                                                                                
                 
                 
                                    

                                                                                        
                                                                                                
                                                                                         
                                                                                     
                                                                             
                                                                              
                              
                                                                
                                                                                    
                                                            
                                                            
                                             
                                                                  
                          
                                                   
                    
                     
                                                         
                                                                                  
                                                               
                                                                                  
                                              
                                                                            
               
                                                      
                   
                  
                                
                                     
                           
                                                                                          
                                                               
                   
                 
                                   
             
           
                     
                                                       
                        
                        
               
                        

end Function

/-! ### Acceptance criteria -/

/-- **Conformance: `(1 2 3) ^ (5 / 3) = 1 2 3 1 2`**, the example of a fractional power of a word
in Adamczewski–Bugeaud. -/
example : [1, 2, 3].rpow (5 / 3 : ℝ) = [1, 2, 3, 1, 2] := by
  have h1 : ⌊(5 / 3 : ℝ)⌋₊ = 1 := by rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h2 : ⌈((5 / 3 : ℝ) - ((1 : ℕ) : ℝ)) * (([1, 2, 3] : List ℕ).length : ℝ)⌉₊ = 2 := by
    rw [show ((5 / 3 : ℝ) - ((1 : ℕ) : ℝ)) * (([1, 2, 3] : List ℕ).length : ℝ) = ((2 : ℕ) : ℝ) by
      norm_num, Nat.ceil_natCast]
  rw [List.rpow, h1, h2]
  rfl

/-- **Conformance: the length of `V ^ w` is `⌈w |V|⌉`**, here `⌈(5 / 3) · 3⌉ = 5`. -/
example : ([1, 2, 3].rpow (5 / 3 : ℝ)).length = 5 := by
  rw [List.length_rpow _ (by norm_num)]
  rw [show (5 / 3 : ℝ) * (([1, 2, 3] : List ℕ).length : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
    Nat.ceil_natCast]


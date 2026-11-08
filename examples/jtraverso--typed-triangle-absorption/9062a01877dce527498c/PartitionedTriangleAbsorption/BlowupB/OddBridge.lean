/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.OddTransformer

/-! # BlowupB.OddBridge — from odd link walks to the type data of the odd transformer

* `LinkWalk.pad`: an odd walk can be lengthened by `2` (back and forth along its last edge);
* `uniform_odd_length`: there is `m₀ = m₀(F)` such that every odd pair `a, b` in every link is
  joined by a walk of length exactly `2m + 1` for every `m ≥ m₀` — one transformer length
  serves all positions;
* `LinkWalk.labels`: a walk as a label sequence;
* `oddTypes_of_labels`: if the path vertices carry the labels of such walks, the type
  conditions `OddTypes` of the odd transformer hold.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedTransformer

variable {t : ℕ} {F : Finset (Multiset (Fin t))} {r : Fin t}

theorem LinkWalk.pad {n : ℕ} {a b c : Fin t} (w : LinkWalk F r n a b) (hc : Link F r b c) :
    LinkWalk F r (n + 2) a b := by
  have := w.append ((LinkWalk.single hc).append (LinkWalk.single ((link_swap F r b c).mp hc)))
  rwa [show n + (1 + 1) = n + 2 by omega] at this

                                                                                 
                           
                                   
               

                                                       
                                                        
                    
                               
                            
                                               
                  
                         
                
                                  
                                                                           

                                               
                                                            
                                                                                              
           
                                               
                                                              
                                             
                                                                              
                                                                           
                                           

theorem LinkWalk.labels {n : ℕ} {a b : Fin t} (w : LinkWalk F r n a b) :
    ∃ f : ℕ → Fin t, f 0 = a ∧ f n = b ∧ ∀ k, k < n → Link F r (f k) (f (k + 1)) := by
  induction w with
  | nil a => exact ⟨fun _ => a, rfl, rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | @cons n a b c hl _ ih =>
    obtain ⟨f, hf0, hfn, hfl⟩ := ih
    refine ⟨fun k => if k = 0 then a else f (k - 1), by simp, by simp [hfn], fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa [hf0] using hl
    · have := hfl (k - 1) (by omega)
      simpa [show k ≠ 0 by omega, show k - 1 + 1 = k by omega] using this

                                     
                                                                                              
                                                                            
                                  
                                                                              
                                                                     
                                                 
                                                                         
                                
                                    
                                                                               
                                                           
                                
                                             
                                                             
             
                    

end PartitionedTriangleAbsorption.BlowupB

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction
public import PartitionedTriangleAbsorption.BlowupB.TeoremaBBalanced

@[expose] public section

/-!
# The trivial-lattice family `Ftriv` on four classes

`Ftriv = {000, 001, 002, 012, 123, 133, 233, 333}`.

Its allowed class pairs are `00, 01, 02, 12, 13, 23, 33`; the forbidden ones are
`03, 11, 22`. Among the 765 families on four classes (up to relabelling) with a forbidden
partner for every class and using all classes, it is the only one whose integral divisibility
on allowed-support graphs is exactly ordinary divisibility (even degrees and `3 ∣ e`), which
satisfies `ThreeStepLinks`, and in which every two classes have a common allowed partner
(census in `PROOF.md`, computed by `scripts/analyze2.py`; this census is exploratory and not
part of the Lean development).

This file records the finite facts, all checked by `decide`.
-/

namespace PaddedTrivial

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer

/-- The trivial-lattice family. -/
noncomputable def Ftriv : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 2, 3}, {1, 3, 3}, {2, 3, 3}, {3, 3, 3}}

theorem Ftriv_card_three : ∀ τ ∈ Ftriv, Multiset.card τ = 3 := by
  unfold Ftriv; decide

/-- The allowed pairs of `Ftriv`: all pairs except `03`, `11`, `22`. -/
def trivAllowed (i j : Fin 4) : Prop :=
  s(i, j) ≠ s(0, 3) ∧ s(i, j) ≠ s(1, 1) ∧ s(i, j) ≠ s(2, 2)

instance (i j : Fin 4) : Decidable (trivAllowed i j) := by
  unfold trivAllowed; infer_instance

theorem Ftriv_allowed_iff : ∀ i j : Fin 4, (∃ k, Link Ftriv i j k) ↔ trivAllowed i j := by
  unfold Link Ftriv trivAllowed; decide

theorem Ftriv_three_step : ThreeStepLinks Ftriv := by
  unfold ThreeStepLinks Link Ftriv; decide

theorem Ftriv_common : ∀ a b : Fin 4, ∃ c,
    (∃ k, Link Ftriv a c k) ∧ (∃ k, Link Ftriv b c k) := by
  unfold Link Ftriv; decide

theorem Ftriv_allowed_of_triangle : ∀ i j k : Fin 4, ({i, j, k} : Multiset (Fin 4)) ∈ Ftriv →
    (∃ a, Link Ftriv i k a) ∧ (∃ a, Link Ftriv j k a) := by
  unfold Link Ftriv; decide

theorem Ftriv_forbidden : ∀ i : Fin 4, ∃ j, ¬ ∃ k, Link Ftriv i j k := by
  unfold Link Ftriv; decide

theorem familyFacts_Ftriv : PaddedGeneral.FamilyFacts Ftriv :=
  ⟨Ftriv_card_three, Ftriv_allowed_of_triangle, Ftriv_forbidden⟩


                                                                        
                                                                           
                                             
                                                                                                
                 

                                                                                        
                                                                                           
                                                                 
                                                              
                                           
                     
                                                                                          
                                                                    
                                                                 
                                                                 
                                                                 
                                                                 
                                                                 
                                                                 
                                                                 
                                                                                     
                                                                       
                                                       
                                                       
                                                                                    
                                                                                  
                                                                                  
                                                                                  
                                                                                  
                                                                                  
                                                                                  
                                                                                  
                                                                                  
                                                                                  
                                                                                   
                                                                                   
                                                                                   
                                                                                   
                                                                                   
                                                                                   
                                                                                   
                         
                    
                    
                    
                     
                      
                           
                                                   
          

                               
                                       

end PaddedTrivial

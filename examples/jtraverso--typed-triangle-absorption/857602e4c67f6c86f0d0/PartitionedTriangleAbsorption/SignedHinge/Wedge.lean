/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Groups
public import Mathlib.Data.Finset.Sym

/-! # Small wedge, copy and vertex-set lemmas used by the signed hinge absorber

Generic in the type family `F`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}

                                                                                           
                                                        
                                                                                   
                                               
                                                                                   
                                                             
       
                                                  
             
                             
                                 
                     
                     
                      
                                      
                                              
           
                                      
                                              
           

                                                                     
                                                                                
                                              
                                                      
       
                           

                                                           
                                                                               
                                                                       
                                                      
       
                       

                       
                                                     
                                                                                      
                                                                                     
                             
                                                            

variable [Fintype V]

theorem mem_vertSet {E : Finset (Sym2 V)} {x : V} : x ∈ vertSet E ↔ ∃ e ∈ E, x ∈ e := by
  simp [vertSet]

                                                                                            
            
                                          
                                      

theorem vertSet_union (E₁ E₂ : Finset (Sym2 V)) :
    vertSet (E₁ ∪ E₂) = vertSet E₁ ∪ vertSet E₂ := by
  ext x
  simp only [mem_union, mem_vertSet]
  constructor
  · rintro ⟨e, he | he, hx⟩
    · exact Or.inl ⟨e, he, hx⟩
    · exact Or.inr ⟨e, he, hx⟩
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    · exact ⟨e, Or.inl he, hx⟩
    · exact ⟨e, Or.inr he, hx⟩

theorem vertSet_pair (x y : V) : vertSet ({s(x, y)} : Finset (Sym2 V)) = {x, y} := by
  ext v; simp [mem_vertSet]

/-- At most two vertices per edge. -/
theorem card_vertSet_le (E : Finset (Sym2 V)) : (vertSet E).card ≤ 2 * E.card := by
  induction E using Finset.induction_on with
  | empty => simp [vertSet]
  | insert e E he ih =>
    rw [card_insert_of_notMem he, insert_eq, vertSet_union]
    induction e using Sym2.ind with
    | _ x y =>
      rw [vertSet_pair]
      refine (card_union_le _ _).trans ?_
      have : ({x, y} : Finset V).card ≤ 2 := card_le_two
      omega

                                                             
                                                      
                                                      
                  
                                    
                                 
            
                        
                                                         
                                                     

end PartitionedTriangleAbsorption.SignedHinge

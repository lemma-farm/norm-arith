/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedBasic

/-! # Deterministic composition of typed physical transformers

This is the algebraic part of an absorber construction, not the existence of
a sparse universal absorber. Union proofs are reused from Aristotle's L0.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- Reused from the returned `Divisibility.lean`, with unchanged proof. -/
theorem IsDecomp.union {E₁ E₂ : Finset (Sym2 V)} {D₁ D₂ : Finset (Finset V)}
    (h₁ : IsDecomp p F E₁ D₁) (h₂ : IsDecomp p F E₂ D₂) (h : Disjoint E₁ E₂) :
    IsDecomp p F (E₁ ∪ E₂) (D₁ ∪ D₂) := by
  obtain ⟨hT₁, hd₁, rfl⟩ := h₁
  obtain ⟨hT₂, hd₂, rfl⟩ := h₂
  refine ⟨fun s hs => ?_, ?_, union_biUnion⟩
  · rcases mem_union.mp hs with hs | hs
    exacts [hT₁ s hs, hT₂ s hs]
  · rw [coe_union]
    refine hd₁.union hd₂ fun s hs s' hs' _ => ?_
    exact h.mono (subset_biUnion_of_mem triEdges hs) (subset_biUnion_of_mem triEdges hs')

/-- Reused from the returned `Divisibility.lean`, with unchanged proof. -/
theorem HasDecomp.union {E₁ E₂ : Finset (Sym2 V)} (h₁ : HasDecomp p F E₁)
    (h₂ : HasDecomp p F E₂) (h : Disjoint E₁ E₂) : HasDecomp p F (E₁ ∪ E₂) := by
  obtain ⟨D₁, hD₁⟩ := h₁
  obtain ⟨D₂, hD₂⟩ := h₂
  exact ⟨_, hD₁.union hD₂ h⟩

/-- An edge-set transformer admits both exact typed decompositions. -/
def IsTransformer (H L R : Finset (Sym2 V)) : Prop :=
  Disjoint H (L ∪ R) ∧ HasDecomp p F (H ∪ L) ∧ HasDecomp p F (H ∪ R)

                                                                                 
                                                                   
                              
                                     
                                                                 
                           
                                                                     

                                                                    
                                                                
                                                             
                                                 
                                                 
                                                                     
                               
                                                           
                                              
                                              
                                              
                                              
                     
                                                          
                                           
                                                      
                                           
                             
                                            
                                                                              
                                                                                      
                                           
                             
                                            
                                                                              
                                                                                      

                                                                                
                                                                                         
theorem IsTransformer.absorbs {H L R : Finset (Sym2 V)}
    (h : IsTransformer (p := p) (F := F) H L R)
    (hR : HasDecomp p F R) (hLR : Disjoint L R) :
    Disjoint (H ∪ R) L ∧ HasDecomp p F (H ∪ R) ∧ HasDecomp p F ((H ∪ R) ∪ L) := by
  refine ⟨disjoint_union_left.mpr ⟨(disjoint_union_right.mp h.1).1, hLR.symm⟩,
    h.2.2, ?_⟩
  have hd : Disjoint (H ∪ L) R := disjoint_union_left.mpr
    ⟨(disjoint_union_right.mp h.1).2, hLR⟩
  simpa only [union_assoc, union_left_comm, union_comm] using h.2.1.union hR hd

end PartitionedTriangleAbsorption

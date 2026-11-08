/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Relabelling preserves the same physical decomposition

Only the allowed triangle types change. The vertices, triangle edge sets,
packing and covered edge set are not replaced. No converse divisibility
implication is asserted.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedCoarseningStage81

open Finset TypedApplicationLinks

variable {V : Type*} [DecidableEq V] {t u : ℕ}

omit [DecidableEq V] in
theorem typedTri_map (p : V → Fin t) (g : Fin t → Fin u)
    (F : Finset (Multiset (Fin t))) (F' : Finset (Multiset (Fin u)))
    (hmap : ∀ τ ∈ F, τ.map g ∈ F') {s : Finset V}
    (hs : IsTypedTri p F s) : IsTypedTri (g ∘ p) F' s := by
  refine ⟨hs.1, ?_⟩
  simpa only [Multiset.map_map] using hmap (s.val.map p) hs.2

theorem decomp_map (p : V → Fin t) (g : Fin t → Fin u)
    (F : Finset (Multiset (Fin t))) (F' : Finset (Multiset (Fin u)))
    (hmap : ∀ τ ∈ F, τ.map g ∈ F') {E : Finset (Sym2 V)}
    {D : Finset (Finset V)} (hD : IsDecomp p F E D) :
    IsDecomp (g ∘ p) F' E D := by
  exact ⟨fun s hs => typedTri_map p g F F' hmap (hD.1 s hs), hD.2⟩

theorem hasDecomp_map (p : V → Fin t) (g : Fin t → Fin u)
    (F : Finset (Multiset (Fin t))) (F' : Finset (Multiset (Fin u)))
    (hmap : ∀ τ ∈ F, τ.map g ∈ F') {E : Finset (Sym2 V)}
    (hE : HasDecomp p F E) : HasDecomp (g ∘ p) F' E := by
  obtain ⟨D, hD⟩ := hE
  exact ⟨D, decomp_map p g F F' hmap hD⟩

                                                         
                                          

                                                        
                          
                                                 
                                                 

                                                             
                                                      
                                  
                                       

end PartitionedTriangleAbsorption.TypedCoarseningStage81

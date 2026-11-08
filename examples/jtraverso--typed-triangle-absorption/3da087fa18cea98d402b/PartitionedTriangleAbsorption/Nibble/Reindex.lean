/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.NearLoadRound

/-! # Restricting a triangle system to surviving triangles, and the schedule

`reindex S s` is the triangle system of the triangles in `s`, indexed by
`Fin s.card`; `reidx s k` is the original index. Each round of the iteration
uses a fresh product space on the current surviving system.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open Finset

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- The original index of the `k`-th element of `s`. -/
noncomputable def reidx (s : Finset (Fin m)) (k : Fin s.card) : Fin m := (s.equivFin.symm k : Fin m)

theorem reidx_mem (s : Finset (Fin m)) (k : Fin s.card) : reidx s k ∈ s :=
  (s.equivFin.symm k).2

theorem reidx_injective (s : Finset (Fin m)) : Function.Injective (reidx s) :=
  fun _ _ h => s.equivFin.symm.injective (Subtype.ext h)

/-- The triangle system restricted to `s`. -/
noncomputable def TriSystem.reindex (S : TriSystem V m) (s : Finset (Fin m)) :
    TriSystem V s.card where
  tri k := S.tri (reidx s k)
  card_tri _ := S.card_tri _
  tri_inj := fun _ _ h => reidx_injective s (S.tri_inj h)

theorem sum_reidx (s : Finset (Fin m)) (f : Fin m → ℝ) :
    ∑ k : Fin s.card, f (reidx s k) = ∑ i ∈ s, f i := by
  rw [← Finset.sum_coe_sort s f]
  exact Equiv.sum_comp s.equivFin.symm (fun x => f x)

theorem sum_reidx_filter (s : Finset (Fin m)) (p : Fin m → Prop) [DecidablePred p]
    (f : Fin m → ℝ) :
    ∑ k ∈ univ.filter (fun k => p (reidx s k)), f (reidx s k) = ∑ i ∈ s.filter p, f i := by
  rw [sum_filter, sum_filter]
  exact sum_reidx s (fun i => if p i then f i else 0)

theorem reindex_load (S : TriSystem V m) (s : Finset (Fin m)) (w : Fin m → ℝ) (e : Sym2 V) :
    (S.reindex s).load (fun k => w (reidx s k)) e =
      ∑ i ∈ s.filter (fun i => e ∈ triEdges (S.tri i)), w i := by
  unfold TriSystem.load TriSystem.edgeTris
  exact sum_reidx_filter s (fun i => e ∈ triEdges (S.tri i)) w

theorem reindex_availLoad (S : TriSystem V m) (s : Finset (Fin m)) (B : Finset (Sym2 V))
    (w : Fin m → ℝ) (e : Sym2 V) (ω : Fin s.card → Bool) :
    availLoad (S.reindex s) B (fun k => w (reidx s k)) e ω =
      ∑ i ∈ s.filter (fun i => e ∈ triEdges (S.tri i) ∧
        triEdges (S.tri i) ⊆ (S.reindex s).untouched B ω), w i := by
  unfold availLoad TriSystem.edgeTris
  rw [filter_filter]
  exact sum_reidx_filter s (fun i => e ∈ triEdges (S.tri i) ∧
    triEdges (S.tri i) ⊆ (S.reindex s).untouched B ω) w

theorem reindex_packEdges (S : TriSystem V m) (s : Finset (Fin m)) (ω : Fin s.card → Bool) :
    (S.reindex s).packEdges ω =
      (((S.reindex s).packing ω).image (reidx s)).biUnion (fun i => triEdges (S.tri i)) := by
  unfold TriSystem.packEdges
  rw [image_biUnion]
  rfl

/-! ## The schedule -/

                                                                       
                                                             
                                                   
                                                                  
                                   
                                                                      
                                                      
                                                          
                                           
                                                        
                               
                                           
                                                                           
                        
                                                            
                       
                                      
                                                   
                                                      
                                                          
                                         
                                 
                                   
                                            
                                         
                                                                     
                                                        
                                                            
                     
                                           
                                             
                                                               
                                         
                                                       
                                                                            
             

end PartitionedTriangleAbsorption.Nibble

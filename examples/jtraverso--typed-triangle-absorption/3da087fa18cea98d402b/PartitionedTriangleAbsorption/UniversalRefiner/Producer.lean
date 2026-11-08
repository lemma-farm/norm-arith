/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Assembly

/-!
# The producer, for an abstract hub hierarchy

`producer_of_hierarchy`: for any hub maps whose link families end empty and whose maps have
no fixed point on link endpoints, any root load bound `r`, auxiliary quota `q` and the strict
selection budget of `AntiEdgeSelection.exists_compatible_family`, there is a fixed physical
library refining every divisible leftover of `X` (`RefinerAssembly.RefinesReserve`), with
explicit size and incidence bounds.  The concrete hub hierarchy and the numerical budgets are
supplied in `UniversalRefiner.Main`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset AntiEdgeSelection OnePart

variable {V : Type*} [DecidableEq V]

theorem pos_enum {C : Finset (LibIdx V)} {k : ℕ} (hk : k < C.card) :
    pos C (enum C k) = k := by
  unfold pos
  rw [dite_eq_left (enum_mem hk)]
  unfold enum
  simp only [dite_eq_left hk, Subtype.coe_eta, Equiv.apply_symm_apply]

omit [DecidableEq V] in
theorem sum_range_enum {C : Finset (LibIdx V)} (g : LibIdx V → ℕ) :
    ∑ k ∈ range C.card, g (enum C k) = ∑ i ∈ C, g i := by
  classical
  refine sum_nbij' (enum C) (pos C) ?_ ?_ ?_ ?_ ?_
  · intro k hk; exact enum_mem (mem_range.mp hk)
  · intro i hi; exact mem_range.mpr (pos_lt hi)
  · intro k hk; exact pos_enum (mem_range.mp hk)
  · intro i hi; exact enum_pos hi
  · intro k _; rfl

theorem card_physU_le (rt : Req V → V × V) (f : Req V → V) (A : Finset (Atom V)) :
    (physU rt f A).card ≤ 2 * A.card := by
  unfold physU
  refine card_biUnion_le.trans ?_
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum fun a _ => card_phys_le rt f a

theorem incidentLoad_physU_le (rt : Req V → V × V) (f : Req V → V) (A : Finset (Atom V))
    (v : V) : incidentLoad (physU rt f A) v ≤ ∑ a ∈ A, incidentLoad (phys rt f a) v := by
  unfold incidentLoad physU
  rw [filter_biUnion]
  exact card_biUnion_le

theorem card_piece_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (i : LibIdx V) :
    (piece X hmap i).card ≤ 11 := by
  cases i with
  | alt l π x ca cb cs => exact card_altAtoms_le π x ca cb cs
  | cyc l σ => exact card_le_two.trans (by norm_num)
  | adj k => exact card_le_two.trans (by norm_num)

variable [Fintype V]

theorem theReqs_roots_ne {X : Finset (Sym2 V)} {hmap : ℕ → V → V} {L : ℕ} {mdr : ℕ → V × V}
    {adr : V × V} (hfix : ∀ l < L, ∀ π ∈ links X hmap l, ∀ u ∈ π, hmap l u ≠ u)
    (hmd : ∀ k, (mdr k).1 ≠ (mdr k).2) (had : adr.1 ≠ adr.2) :
    ∀ r ∈ theReqs X hmap L mdr adr,
      (rootPair hmap mdr adr r).1 ≠ (rootPair hmap mdr adr r).2 := by
  intro r hr
  simp only [theReqs, allReqs, mem_union] at hr
  rcases hr with (hr | hr) | hr
  · have hA : (Sum.inl r : Atom V) ∈ parRem X hmap L := by
      rw [parRem_eq]; exact mem_image_of_mem _ hr
    obtain ⟨l, hl, hA⟩ := mem_biUnion.mp hA
    cases r with
    | ep l' u j b =>
      obtain ⟨rfl, hj⟩ := ep_mem_levelAtoms.mp hA
      obtain ⟨π, hπ⟩ : (vChain (links X hmap l') u).Nonempty := card_pos.mp (by omega)
      obtain ⟨hπ, hu⟩ := mem_vChain.mp hπ
      exact (hfix l' (mem_range.mp hl) π hπ u hu).symm
    | pr l' σ j b =>
      obtain ⟨-, hσ, -⟩ := pr_mem_levelAtoms.mp hA
      exact endA_ne_endB (mem_nextLinks.mp hσ).2
    | tm l' σ b =>
      obtain ⟨-, hσ⟩ := tm_mem_levelAtoms.mp hA
      exact endA_ne_endB (mem_nextLinks.mp hσ).2
    | md k c b => exact absurd hA md_not_mem_levelAtoms
    | adj k b => exact absurd hA adj_not_mem_levelAtoms
  · obtain ⟨k, -, hk⟩ := mem_biUnion.mp hr
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact had
  · obtain ⟨q, -, rfl⟩ := mem_image.mp hr
    exact hmd q.1

omit [Fintype V] in
theorem card_layeredPiece_le {N : ℕ} {B : ℕ → Finset (Sym2 V)} {W : ℕ → Fin 3 → Finset (Sym2 V)}
    (hB : ∀ i < N, (B i).card ≤ 22) (hW : ∀ i c, (W i c).card ≤ 4)
    {j : ℕ × Bool × Fin 3 × Fin 3} (hj : j.1 < N) :
    (ModThreeLayer.layeredPiece N B W j).card ≤ 42 := by
  obtain ⟨i, sel, a, b⟩ := j
  have h1 : (if sel then B i else ∅).card ≤ 22 := by
    split_ifs
    · exact hB i hj
    · simp
  have h2 : (ModThreeLayer.leftPart W i a).card ≤ 12 := by
    unfold ModThreeLayer.leftPart
    split_ifs
    · simp
    · refine card_biUnion_le.trans ((sum_le_sum fun k _ => hW (i - 1) k).trans ?_)
      rw [sum_const, smul_eq_mul]
      have : (univ.filter fun k : Fin 3 => a ≤ k).card ≤ 3 :=
        (card_filter_le _ _).trans (by simp)
      omega
  have h3 : (ModThreeLayer.rightPart N W i b).card ≤ 8 := by
    unfold ModThreeLayer.rightPart
    split_ifs
    · refine card_biUnion_le.trans ((sum_le_sum fun k _ => hW i k).trans ?_)
      rw [sum_const, smul_eq_mul, ModThreeLayer.card_filter_lt]
      have := b.isLt
      omega
    · simp
  unfold ModThreeLayer.layeredPiece
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
  simp only at h1 h2 h3 ⊢
  omega

                                                      
                                                                                            
                                                                                    
                                                                 
                                                                                            
                                                                                         
                
                                                                                            
                                                   
                                                                                
                                     
                                                                                   
                                               
                                       
                                                                               
                                                             
                                                                                
                                           
                                                          
                                                                                                 
                                          
                                           
                                                                                               
                                                                                          
                                                                              
                                  
                                               
                                         
                                            
                                                   
                                                    
                  
                                                                     
                                
                                          
                         
                                          
                                      
                                               
                                                                              
                                       
              
                                           
                                                          
                            
                                                      
                                                             
                                                                
                                                                       
                                       
                              
                                                                          
                                            
                                 
              
                                               
                                               
                                                  
              
                                                           
                                                                                             
                                                                                       
                                                                                
                
                                                 
                                                              
                            
                               
               
                                    
                  
                                                                              
                                                      
                                                                                        
                    
                                                     
                                                                                          
                                                                               
                                                                                            
                                                             
              
                                                           
                                                           
                       
                                                                                    
                                
                                                                                    
           
                                                                     
                                       
                                        
                       
         
           
                                                         
                                                      
                                                   
                                                     
                                                                  
                                                                                     
             
                                                                                 
                                                                
                                                       
                                                             
                                       
                                                       
                                                                   
                                                                
                                                                                      
                                             
                                                                                 
                                              
                                                                              
                                                          
               
                                                       
                                                                                                
                                                                                
                 
                                                                             
         

end PartitionedTriangleAbsorption.UniversalRefiner

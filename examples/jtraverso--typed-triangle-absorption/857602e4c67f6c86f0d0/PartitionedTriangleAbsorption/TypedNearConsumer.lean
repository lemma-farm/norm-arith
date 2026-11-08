/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.NearConsumer
public import PartitionedTriangleAbsorption.TypedCoverDownConsumer

/-! # Typed nibble and cover-down without exact fractional repair

The positive tolerance is chosen before the graph. A supplied anti-edgeful
reserve supplies the degree gap required by the near-load nibble. The final
consumer still requires a single supplied universal absorber and weights on
the actual main graph. It does not construct either missing input.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedNearConsumer

open Finset TypedNibble TypedCoverDown

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem exists_type_of_load_pos (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) (φ : Finset V → ℝ) {a b : V}
    (hload : 0 < ∑ s ∈ copies p F J with s(a, b) ∈ triEdges s, φ s) :
    ∃ k : Fin t, ({p a, p b, k} : Multiset (Fin t)) ∈ F := by
  obtain ⟨s, hs, -⟩ := exists_ne_zero_of_sum_ne_zero hload.ne'
  obtain ⟨hsc, hab⟩ := mem_filter.mp hs
  have hcopy := mem_copies_iff.mp hsc
  obtain ⟨ha, hb, hne⟩ := mem_triEdges_iff.mp hab
  obtain ⟨c, hac, hbc, rfl⟩ := exists_third_of_card_three hcopy.1.card_eq ha hb hne
  refine ⟨p c, ?_⟩
  rw [← map_three p hne hac hbc]
  exact hcopy.2

/-- The reserve forces a degree gap at every vertex incident to a typeable
main edge. Vertices with no main edges require no population assumption. -/
theorem degree_gap_of_reserve (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) [DecidableRel J.Adj] (X : Finset (Sym2 V))
    [DecidableRel (ReserveCoverDown.reserveGraph X).Adj]
    (α : ℝ) (hα : α ≤ 1) (hdis : Disjoint J.edgeFinset X)
    (hres : AntiEdgeful p F (ReserveCoverDown.reserveGraph X) α)
    (htype : ∀ a b, J.Adj a b → ∃ k, ({p a, p b, k} : Multiset (Fin t)) ∈ F) :
    DegBounded J.edgeFinset ((1 - α) * Fintype.card V) := by
  classical
  intro v
  by_cases hempty : Nibble.star J.edgeFinset v = ∅
  · change ((Nibble.star J.edgeFinset v).card : ℝ) ≤ _
    rw [hempty, card_empty, Nat.cast_zero]
    exact mul_nonneg (sub_nonneg.mpr hα) (Nat.cast_nonneg _)
  obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr hempty
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp (mem_filter.mp he).2
  have hvu : J.Adj v u := J.mem_edgeFinset.mp (mem_filter.mp he).1
  obtain ⟨k, hk⟩ := htype v u hvu
  let W := univ.filter (fun w => (ReserveCoverDown.reserveGraph X).Adj v w ∧
    (ReserveCoverDown.reserveGraph X).Adj w u ∧ p w = k)
  have hW : α * Fintype.card V ≤ (W.card : ℝ) :=
    hres _ hk _ _ _ rfl v u hvu.ne rfl rfl
  have hc : W.card ≤ (Nibble.star X v).card := by
    apply card_le_card_of_injOn (fun w => s(v, w))
    · intro w hw
      have hadj := (mem_filter.mp hw).2.1
      change s(v, w) ∈ X ∧ v ≠ w at hadj
      exact mem_filter.mpr ⟨hadj.1, by simp⟩
    · intro w _ w' _ heq
      rcases Sym2.eq_iff.mp heq with h | h
      · exact h.2
      · exact h.2.trans h.1
  have hsum : (Nibble.star J.edgeFinset v).card + (Nibble.star X v).card ≤ Fintype.card V := by
    unfold Nibble.star
    rw [← card_union_of_disjoint (hdis.mono (filter_subset _ _) (filter_subset _ _))]
    rw [← filter_union]
    exact Nibble.card_star_le _ _
  have hcR : (W.card : ℝ) ≤ (Nibble.star X v).card := by exact_mod_cast hc
  have hsR : ((Nibble.star J.edgeFinset v).card : ℝ) + (Nibble.star X v).card ≤
      Fintype.card V := by exact_mod_cast hsum
  change ((Nibble.star J.edgeFinset v).card : ℝ) ≤ _
  nlinarith

                                                                           
                                                                                      
                                         
                                                                    
                                                                                   
                                                
                                                                    
                                                            
                                                                                       
                                                       
                                                                        
                                              
                                                                  
                                                                         
                            
                                          
                                                                                     
                         
                                                                    
                                                   
                                                        
                                                           
                                 
                                               
                                                                                 
              
                                         
                                    
              
                                           
                                         
                                                                  

                                                                         
                                                                               
                                                               
                                 
                                         
                                                                    
                                                               
                                                                        
                                                                                
                                                            
                                   
                                                           
                                                             
                                                                                       
                                               
                                      
                                                                                       
                                                 
                                        
                                                                                
                       
                                                
                                                                  
           
                                                                   
                                                                                         
                                                                                       
              
                                                
            
                                                                                   
                 
                                                                             
                                           
           
                                                                    
                                                                  
                                             
                                                           
                                     
                     
                                       
                                                 
                                                                            
                                                                    
                                           
                                    
                                                                                               
                                                                                 
                                                                                          
                                                        
               
                                                                            

end PartitionedTriangleAbsorption.TypedNearConsumer

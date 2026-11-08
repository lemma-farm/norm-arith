/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedEmbeddingSelection
public import PartitionedTriangleAbsorption.PairMoveStage85

/-! # Selection from compatible four-root supply

Unlike the older `Supply`, this hypothesis only queries compatible labels.
All forbidden vertices, including every active vertex, are explicitly excluded.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairMoveSelectionStage85

open Finset RootedEmbeddingSelection AntiEdgeSelection TypedEmbeddingSelection
open TypedTransformer

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def Compatible (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (S : Finset V) (i : Fin t) : Prop :=
  ∀ v ∈ S, ∃ k, Link F i (p v) k

/-- The proposed hypothesis R, with its count expressed as a single real `a`. -/
def CompatibleSupply (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) : Prop :=
  ∀ S : Finset V, S.card ≤ 4 → ∀ i, Compatible p F S i →
    a ≤ ((typedNeighbours p G S i).card : ℝ)

/-- Select the real auxiliary from the stated compatible supply, not from an
uninterpreted oracle. Choosing Z to contain the configuration support fixes
the future-edge collision in the originally supplied exchange proof. -/
theorem exists_fresh (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hs : CompatibleSupply p F G a) (S Z : Finset V) (i : Fin t)
    (hS : S.card ≤ 4) (hi : Compatible p F S i)
    (B : Finset (Sym2 V)) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hb : (Z.card : ℝ) + 4 * d < a) :
    ∃ w, p w = i ∧ (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧
      ∀ u ∈ S, s(u, w) ∉ B := by
  let W := typedNeighbours p G S i
  have hsum : (∑ u ∈ S, (incidentLoad B u : ℝ)) ≤ 4 * d := by
    calc
      _ ≤ (S.card : ℝ) * d := by
        simpa only [incidentLoad, sum_const, nsmul_eq_mul] using
          (sum_le_sum (s := S) fun u _ => hB u)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hd
  have hcount := available_card_budget W Z S B
  have hpos : 0 < (W \ (Z ∪ blockedMany B S)).card := by
    by_contra h
    have hz : (W \ (Z ∪ blockedMany B S)).card = 0 := by omega
    rw [hz, Nat.zero_add] at hcount
    have hr : (W.card : ℝ) ≤ Z.card + ∑ u ∈ S, (incidentLoad B u : ℝ) := by
      exact_mod_cast hcount
    have hsupply := hs S hS i hi
    change a ≤ (W.card : ℝ) at hsupply
    linarith
  obtain ⟨w, hw⟩ := card_pos.mp hpos
  obtain ⟨hw, hbad⟩ := mem_sdiff.mp hw
  have htyped := (mem_filter.mp hw).2
  refine ⟨w, htyped.1, htyped.2, ?_, ?_⟩
  · intro hz
    exact hbad (mem_union.mpr (Or.inl hz))
  · intro u hu he
    exact hbad (mem_union.mpr (Or.inr (mem_biUnion.mpr
      ⟨u, hu, mem_filter.mpr ⟨mem_univ _, he⟩⟩)))

omit [Fintype V] in
/-- Combine forbidden and previously used edges without assuming sparsity of U. -/
theorem blocked_union_degree (B U : Finset (Sym2 V)) (d : ℝ)
    (hB : DegBounded B d) : DegBounded (B ∪ U) (d + U.card) := by
  intro v
  have hc : ((B ∪ U).filter (fun e => v ∈ e)).card ≤
      (B.filter (fun e => v ∈ e)).card + U.card := by
    rw [filter_union]
    exact (card_union_le _ _).trans
      (Nat.add_le_add_left (card_le_card (filter_subset _ _)) _)
  have hcr : (((B ∪ U).filter (fun e => v ∈ e)).card : ℝ) ≤
      ((B.filter (fun e => v ∈ e)).card : ℝ) + U.card := by exact_mod_cast hc
  linarith [hB v]

                                                                                  
                                                                                 
                                                      
                                                                
                                               
                                                              
                                                  
                                                 
                                    
                                                                
                                                   
          

theorem rotate_link {i j k : Fin t} {F : Finset (Multiset (Fin t))}
    (h : Link F i j k) : Link F k i j :=
  (link_root_swap F i k j).mp ((link_swap F i j k).mp h)

                                                                       
                                                                    
                                                                              
                                                                                      
                                                                               
                                                      
                                                                  
                                                    
                                                        
                                        
                                 
                                                              
                                                  
            
                                                                     
                                               
                                                 
                                                                          
                                          
                                      
                              
                                                          
                                                      
                                    
              
         
                                       
              
                                                   
                                  
                                     
                 
                                     
                                                                               
                                    
                                                                       
                                          
                              
                                                              
                                                          
                                                      
                                     
              
         
                                       
              
                                                   
                                        
                                     
                 
                                     
                                                                               
              
                                                                        
                                    
                                                                       
                                          
             
                        
                                          
             
                        
                                                  
                                                                               
                                                            
                                                   
                                                                               
                                                                          
                                                                          
              
                                             
                                                                          
              
                                             
                                                
            
                                             
                                                        
                                 
                                 
                                 
                                 
                                 
                                 
                                 

                                                                               
                                                                             
                                                                               
                                                                              
                                                                              
                                                                  
                                                    
                                            
                                            
                                                              
                                                  
                    
                                                                    
                                     
                                                                    
                                                                    
                                                                      
                                                                             
                                                                                   
                                                                                         
                                   
                                                                     
                                                 
                                                                        
                  
                                                     
                                                          
           
                       
                                                         
                                                                                       
                                                                                         
                                                                                         
                                                                                              
                                                                          
                                                                   
                                                       
                                                                 
                                                             
                                                        
             
                                   
                            
                                           

end PartitionedTriangleAbsorption.PairMoveSelectionStage85

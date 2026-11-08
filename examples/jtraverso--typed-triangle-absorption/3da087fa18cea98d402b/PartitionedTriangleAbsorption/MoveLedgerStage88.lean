/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalMovesFrameStage87
public import PartitionedTriangleAbsorption.PairSplitDeploymentStage87

/-! # Recovering the final move ledger and inserting later catalysts

A deployment theorem returns a configuration and a trace. Subsequent choices
must avoid every edge ever used, not just the last configuration. The theorem
below extracts that finite ledger from the trace, with its exact budget, and
restricts the trace's added edges to the ledger. Decomposable catalysts chosen
outside this ledger can then be inserted retrospectively without breaking any
earlier freshness condition. This does not select the catalysts or finish the
token-cut/cleanup producer.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.MoveLedgerStage88

open Finset PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- Extract a real terminal ledger. The supported trace can subsequently be
continued from precisely this ledger, and all its added edges lie in it. -/
theorem terminal_ledger {E B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n) (hX : X ⊆ U) :
    ∃ L : Finset (Sym2 V), U ⊆ L ∧ Y ⊆ L ∧ L.card ≤ U.card + 9 * n ∧
      PhysicalMoves p F (E ∩ L) B U X Y n ∧
      (∀ Z m, PhysicalMoves p F E B L Y Z m →
        PhysicalMoves p F E B U X Z (n + m)) := by
  induction h with
  | stop U X =>
    refine ⟨U, Subset.refl _, hX, by simp, .stop _ _, ?_⟩
    intro Z m hm
    simpa using hm
  | @step U X Y Q R H n hx hq hf hphys hm hH hR ht ih =>
    have hnext : (X \ Q) ∪ R ⊆ U ∪ H ∪ R := by
      intro e he
      simp only [mem_union, mem_sdiff] at he ⊢
      rcases he with ⟨he, _⟩ | he
      · exact Or.inl (Or.inl (hx he))
      · exact Or.inr he
    obtain ⟨L, hUL, hYL, hc, hsmall, hcont⟩ := ih hnext
    have hUL' : U ⊆ L := by
      intro e he
      exact hUL (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl he))))
    have hHRL : H ∪ R ⊆ L := by
      intro e he
      rcases mem_union.mp he with he | he
      · exact hUL (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr he))))
      · exact hUL (mem_union.mpr (Or.inr he))
    refine ⟨L, hUL', hYL, ?_, .step hx hq hf
      (fun e he => mem_inter.mpr ⟨hphys he, hHRL he⟩) hm hH hR hsmall, ?_⟩
    · have h1 := card_union_le (U ∪ H) R
      have h2 := card_union_le U H
      omega
    · intro Z m hz
      have htail := hcont Z m hz
      have hall := PhysicalMoves.step hx hq hf hphys hm hH hR htail
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

                                                                            
                                                                           
                                                                   
                                                                   
                                                      
                                                                    
                                            
                                                              
                                                         
                              
             
                                                                 
                                           
                                                        
                                                                
                                             
                    

                                                                        
                                                
                                                                     
                                                                           
                                                                         
                                            
                                                              
                                                            
                                                   
                                              

                                                                              
                                                                         
                                                                                 
                                                      
                                                            
                                            
                                      
                                                               
                                  
                                                                            
                                                            
                                                              
                         
                                                
                                                    
                                                 
                                                         
                                                    
                                            
                                                                         
                                                  
                                                                   
                                  
                                                                     
                                                                     

                                                                           
                                               
                                                     
                                       
                                               
                                        
          

end PartitionedTriangleAbsorption.MoveLedgerStage88

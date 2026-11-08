/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.Main
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.HostSupply
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedLedger
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.FiniteLibrary
public import PartitionedTriangleAbsorption.ColouredHub.Families

/-! # A fixed universal F3 absorber in a guarded extendible host

The refiner, the finite abstract terminal templates, their physical embeddings,
and the complete private family are constructed in this theorem.  The scalar
premises are numerical budgets, with constants chosen before the host.  There
is no completeness, refiner-existence, or absorber-existence premise.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset AntiEdgeSelection TypedApplicationLinks TypedTransformer

/-- The full universal quantifier over residues, with explicit density scales. -/
def UniversalAbsorbers {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ρ δ : ℝ) : Prop :=
  ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset → DegBounded X (2 * ρ * Fintype.card V) →
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
      HasDecomp p F A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
      ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)

theorem F3_allowed_iff : ∀ i j : Fin 4, (∃ k, Link F3 i j k) ↔ i ≠ j := by
  unfold Link F3
  decide

                             
                              
                                               
                                                                  
                          
                                            
                                                                       
                                                         
                                
                                                                       
                                                                         
                                          
                                                        
                                                                
                                               
                                                                                                     
                                 
                              
                                                       
                                                      
                                                                                    
                                                                              
           
                             
                                       
                          
               
                                                        
                             
                             
                   
                                             
                                                                             
                     
                                                                   
                                                                        
                                
                       
                                                                     
                                                        
                                    
                                                                  
                            
                
                                                                             
                                                                      
                                                    
                                                                   
                                       
                     
             
        
                                                            
                                            
                                                                
                                                            
                                                                        
                                 
                                        
             
                                                                                     
                                                                                                
                                                    
                                                                     
                                                                    
        
                                                                                
                
                                                                             
                                       
                                                                                              
                       
                                      
                                                                                       
                                                                            
                                                                      
                                                                                 

                                 

end PartitionedTriangleAbsorption.StructuralF3General

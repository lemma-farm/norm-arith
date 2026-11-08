/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.FiniteSupport
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedEmbedding

/-!
# Bounded terminal absorbers in a host with guarded supply

The coefficient bound is chosen before the host, ledger and piece.  Each
piece is first restricted to its numbered finite support; the existing
coloured-hub template is then embedded with all roots fixed.  This proves
a terminal construction and makes no assertion about simultaneous choices
for a family of pieces or about weights after deleting their union.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset AntiEdgeSelection TypedTransformer TypedDivisibilityCollapse

universe u

def terminalOrder (K B t : ℕ) : ℕ := 36 * K + 105 * B + t

def terminalSize (K B : ℕ) : ℕ := 105 * K + 318 * B

structure TerminalAbsorber {V : Type u} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P L : Finset (Sym2 V)) (Z : Finset V) (C : ℕ)
    (A : Finset (Sym2 V)) : Prop where
  subgraph : A ⊆ G.edgeFinset
  avoidLedger : Disjoint A L
  avoidPiece : Disjoint A P
  decomp : HasDecomp p F A
  decomp_union : HasDecomp p F (A ∪ P)
  card_le : A.card ≤ C
  vertices : ∀ v ∈ vertSet A, v ∈ vertSet P ∨ v ∉ Z
  no_root_edge : ∀ v ∈ vertSet P, ∀ w ∈ vertSet P, s(v, w) ∉ A
  root_load : ∀ v ∈ vertSet P, incidentLoad A v = 4 * incidentLoad P v

                                                                                   
                                                                         
                                                                          
            
                                                
                                                                
                                                       
                                                                                
                              
                                                                        
                                                                 
                      
                                                                                    
           
                                                                   
                                                                              
                        
           
                                                                                     
                                                     
                    
                    
                    
                              
                                                             
                                     
                          
                                           
                                 
                                       
                                              
                               
                                                                   
                                                                        
                                                                      
                                                   
                                         
                                                                                       
                                               
                                                                                             
                                                      
                  
                                                    
                                    
                                                
                                  
                     
                                                      
                                                      
                                                                         
                                                                              
                                                             
                                               
                      
               
                                         
                                                                             
                   
                                                                 
                                                  
                                                            
                                                   
                                              
                                                                          
                                                                                        
                          
           
                                                                                         
                                                                                
                                                        
              
                                                          
                 
                           
                                             
                                              
                                                                           
                           
                                             
                                              
                                                                                 
                                                            
                
                                           
                           
                                                                            
                                                            
                                                                              
                                                                                  
                                                    
                                                                
                                                                               
                                                                             
             
              
                                     
                    
                                                                     
                                                                               
                           
                                                              
                                                                        
                
                                       
                                                
              
                                
                                         
                
                                              
                                      
                
                                                                             
                                  
                        
                    
                                              
                                      
                                                         
                                     
                                                                               
                            
                  
                                      
                                                                  
                                                
                                                                             
                                     
                                                                  
                
                                                          
                                              
                                               
                         
                                             
                 
                                               
                                   
                                                                       
                           
                                                        
                                                        
                          
                          
                                               
                                                             
                                                        
                                                      
             
                         
                                                                                 
                
                                                        
          
                                                                         
                                                                                              
                                                
                                                                         
                                                                                         
                                      

                                       

end PartitionedTriangleAbsorption.StructuralF3General

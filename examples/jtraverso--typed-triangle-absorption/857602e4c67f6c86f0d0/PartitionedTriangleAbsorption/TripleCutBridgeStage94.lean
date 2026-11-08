/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TripleCutInductionStage94

/-! # From the accepted insertion return to the triple cuts

`initial_phys` and `initial_bdry` show that the final state of the accepted
catalyst insertion (`TypedCatalystBridgeStage93.catalyst_producer`) is a
physical token state satisfying the boundary invariant with all original
tokens remaining. The active set used for the cuts is the insertion's
forbidden set `Z₀` together with all carriers. The proof uses the accepted
incidence identities `tokAt_cz`, `tokAt_cz'`, `tokAt_cs`, `tokAt_ct`,
`tokAt_other`, `tokPos_injOn`, the carrier labels and
`original_token_type`; no new distinctness hypothesis is supplied.

`triple_cut_producer` composes deployment, catalyst selection, insertion and
the cut of an arbitrary given disjoint family of valid target triples of the
deployed original tokens into one physical trace, with explicit budget
`|Z| + 272 |X| + 4 (d + |U|) < a`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TripleCutStage94

open Finset AntiEdgeSelection TypedTransformer CatalystSelectionStage89
  CatalystInsertionStage89 PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- The empty edge set decomposes. -/
theorem hasDecomp_empty {p : V → Fin t} {F : Finset (Multiset (Fin t))} :
    HasDecomp p F (∅ : Finset (Sym2 V)) :=
  ⟨∅, fun _ h => absurd h (notMem_empty _), by simp, by simp⟩

                                                                                 
                                             
                   
                     
                    
                     
                                           
                             
                                           

                                                                                
                                                                    
                                                                 
                                                               
                                           
                   
               
                   
                                  
                                                                        
                                   
                                                                                       
                                                                          
                                                                                  
        

                                                                            
                                                                                  
                                                    
                                                     
                             
                                                                         
                                                                                      
                                                     
                                  

variable [Fintype V]

section initial

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  [DecidableRel G.Adj] {B : Finset (Sym2 V)} {S : Data V} {Z₀ : Finset V} {cz cz' : V → V}
  {U : Finset (Sym2 V)} {Z : Finset V}

                                                                        
                                                                                           
                                                                                        
             
                                                               
                             
                         

                                                                            
                   
                                              
                                             
                                                                                
                                           
                                                                                          
           
                   
                                                                       
                               
                          
                                                           
                                               
                                 
                                 
                      
                                                           

                   
                                                
                                                                        
                      
                                                         
                                               
                                                
       

                                                                           
                            
                                              
                                             
                                              
                         
                                                            
             
                                                              
                   
                                                  
             
                                                                    
                                          
                                                
                                         
             
                                                                     
                                          
                                                 
                                          
                                       
                                       
                   
                                                           
                             
                                                                                           
                                                                                             
                                          
              
                                       
             
                                                           
                                                
                                                                                     
                                                                                      
                                 
                 
                                                            
                                                
                                                          
                                                          
          
                                             
                          
                               

end initial

                                                                            
                                                                            
                                                                         
                                                                           
                                                                           
                                                                              
                                                            
                                            
                                      
                                                               
                                  
                                                           
                                          
                                                               
                                                                   
                                                                            
                                                                     
                                      
                                      
                                                                
                                                                   
                                            
                                                               
                                                                              
                                                                         
                                                                                 
                                    
                                                                         
                                                                                
                                                                         
                                                        
                                                                                    
                                                   
                                                                                          
                                                
                                                                                
                                                                        
                                                          
                                                  
                                                                                         
                                                           
                                                                                              
                         
                                           
                                               
                                                  
                                                                           
         
                                                                                    
                               
                                                                                           
                                                                       
                                  
                                                     
                                                                
         
                                 
                                 
                                                             
                                                                     
                        
                                          
                                       
                           
                                                                     
                                                                                        
                               
                        
                                                                           
                                                                                      
                                                 
                                                                    
                       
                                                                          
                                     
                                                                                   
                   
                
                                              
                                                                                             
                   

end PartitionedTriangleAbsorption.TripleCutStage94

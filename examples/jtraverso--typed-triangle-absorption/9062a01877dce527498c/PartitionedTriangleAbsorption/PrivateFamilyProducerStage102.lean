/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.DivisiblePrivateAbsorberStage101
public import PartitionedTriangleAbsorption.RefinerAssembly

/-! # A physical private family fixed before residual selection

All absorbers are produced by Stage101. Their edge sets avoid the whole piece
support J and are mutually disjoint. The size budget is global; this does not
claim a sparse refiner or a degree-efficient family for a quadratic library.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateFamilyStage102

open Finset TypedTransformer PairMoveAssemblyStage85 PairMoveSelectionStage85
  AntiEdgeSelection

variable {t : ℕ} {I V : Type*} [DecidableEq I] [DecidableEq V] [Fintype V]
  {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- The actual produced family, including its physical union bound. -/
structure Family (s : Finset I) (P : I → Finset (Sym2 V))
    (B J E : Finset (Sym2 V)) (C : ℕ) (A : I → Finset (Sym2 V)) : Prop where
  absorbs : ∀ i ∈ s, Absorbs (p := p) (F := F) (A i) (P i)
  avoids : ∀ i ∈ s, Disjoint (A i) (B ∪ J)
  size : ∀ i ∈ s, (A i).card ≤ C
  physical : ∀ i ∈ s, A i ⊆ E
  disjoint : (s : Set I).PairwiseDisjoint A
  total : (s.biUnion A).card ≤ s.card * C

                                                                             
                                                                            
                                                             
                                                                   
                                                                       
                                                              
                                                
                                                                      
                                           
                                                                 
                                              
                                
                                                            
                                                                                   
                                                                                          
                                                                    
           
                           
                                      
                                                                  
           
                                              
              
             
                             
                          
                          
               
                                                               
                                                   
                              
                                                   
                          
                                 
                                          
                                  
                        
                                    
                                                              
                                      
                                                          
                  
                              
                                                                
                                                               
                                                
                                                 
                                       
                                                                  
                                                                     
                                                
                                                                             
                                                                   
                                                                       
                                                                            
                                                              
                                                          
                                                
                                                                            
                                      
                                                                             
                                        
                                                                     
                                  
                                                                      
                                     
                          
                     
                              
                                                
                                 
                                                                           
                                        
                                      
                                                     
                                                               
                                                         
                                                    
                  
                                                                       
                                                        
                  
                                             
                                       
                                                     
                     
                 
                  
                                             
                                      
                                                        
                  
                                             
                                                                       
                                                       
                 
                  
                                             
                                       
                                                         
                           
                                     
                            
                 
                                                                   
                                                           
                                                         
                              
                   
                                                                    
                                                           
                                                                 
                                            
                                                                     
                               

end PartitionedTriangleAbsorption.PrivateFamilyStage102

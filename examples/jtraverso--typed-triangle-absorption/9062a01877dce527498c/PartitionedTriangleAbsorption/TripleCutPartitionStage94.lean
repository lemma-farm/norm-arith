/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TripleCutBridgeStage94

/-! # Cutting a given partition of all remaining original tokens

If the given disjoint family of valid target triples covers exactly the
remaining original tokens, then after `cut_all` no original token remains:
all original tokens sit in isolated allowed triangles, their edges have an
actual decomposition, and every vertex carries nothing, exactly two catalytic
tokens, or exactly two original tokens of one finished triangle.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TripleCutStage94

open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89 PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] [Fintype V] {t : ℕ}

                                                                      
                                                                     
                                                                            
                                                                                    
                                                                                  
                                                                 
                                                                
                                  
                                                                                       
                                                                  
                                                                     
                                                            
                                                        
                                 
                                                                            
                                                                                      
                                                                                              
                                                                                              
                                                                                   
                         
                                                                            
                                                                                           
                                                                                 
                                              
                                                                       
                                
                                     
                                                                                

end PartitionedTriangleAbsorption.TripleCutStage94

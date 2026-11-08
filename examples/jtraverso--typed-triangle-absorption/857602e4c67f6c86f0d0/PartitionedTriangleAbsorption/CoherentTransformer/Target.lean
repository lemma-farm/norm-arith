/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoherentTransformer.ChargeInvariant
public import PartitionedTriangleAbsorption.TypedApplicationLinks
public import Mathlib.Basic.Real.Basic

/-! # The candidate coherent F0 transformer target

This module only STATES the candidate target of the Stage46 coherence
request. It is refuted in `CoherentTransformer.Refutation`.

* `trailEdges σ x` is the physical closed-trail graph `{x_i x_(σ i)}`.
* `PhysicalTrail G σ x`: nonloop edges, injective position-to-edge map,
  every edge in `G`. Vertex repetitions are allowed.
* `CloneCondition`: the two-root same-part common-neighbour premise.
* `IsCoherentTransformer`: `T ⊆ E(G)`, edge-disjoint from `Hx ∪ Hy`, and
  both `T ∪ Hx` and `T ∪ Hy` are F0-decomposable.
* `CandidateTarget α β K`: uniform constants `C, N` chosen before the host,
  and a transformer with at most `C|I|` edges and `C|I|` auxiliary vertices.
  The optional root-degree bound is not included: dropping a conclusion only
  makes the refuted statement weaker, hence the refutation stronger.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoherentTransformer

open Finset TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {I : Type*} [Fintype I] [DecidableEq I]

                                                       
                                                                  
                                     

                                                                                        
                                                                              
                                                                        
                              

                       
                                                                                
                                                              
                                       
            
                                                             
                       
                                                          
               

                                   
                                                                                       
                                                
                                                            
                            
                   
                 

                                                                    
                                                                           
                                   
                                        
                                                                             

                                                                            
                                                                                  
                                                                    
                                                                   
                                                                             

                                                                               
                                                                 
                                                                 

                                                                             
                                                                           
                                               
                   
                                                                                
                                                                 
                                       
                                                            
                                                 
                                                 
                                                                         
                                
                                                                
                                           
                                                           

end PartitionedTriangleAbsorption.CoherentTransformer

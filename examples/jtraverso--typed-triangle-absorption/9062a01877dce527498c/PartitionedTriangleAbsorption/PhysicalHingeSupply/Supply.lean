/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Template
public import PartitionedTriangleAbsorption.F0Geometric.CommonNeighbour
public import PartitionedTriangleAbsorption.SignedHinge.Select
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # A physical hinge-supply producer from four-root common-neighbour richness

`hingeSupply_of_commonNbrRich`: for every `ρ > 0` there is `N` (chosen before the host)
such that every host with `N ≤ n` and `CommonNbrRich 4 p G ρ` satisfies the literal
`SignedHinge.HingeSupply p F0 G (ρ^2/4) 6`.

Construction for two actual copies sharing exactly one edge, written `S = {u,v,w}`,
`S' = {u,v,z}` (`roots_of_shared_edge`):

1. `y ∈ yCand`: part `p v`, adjacent to `u, w, z`, not one of the four roots;
2. `x ∈ xCand y`: part `p u`, adjacent to `v, w, z, y`, not one of the four roots
   (hence `x ≠ y`);
3. `H = hingeEdges u v w z x y = {uy, vx, xw, yw, xz, yz, xy} ⊆ E(G)`, a physical hinge
   (`hingeEdges_isHinge`) with `|vertSet H| = 6` (`card_vertSet_hingeEdges`);
4. distinct choices give distinct edge sets: `y` is the unique `H`-neighbour of `u` and `x`
   the unique `H`-neighbour of `v` (`hingeEdges_inj`);
5. each query has at least `ρ n - 4 ≥ ρ n / 2` answers once `ρ n ≥ 8`
   (`card_fresh_ge`), so at least `(ρ n / 2)^2 = (ρ^2/4) n^(6-4)` distinct `H`.

The count is over distinct edge subsets of `G.edgeFinset`, exactly as in `HingeSupply`;
no labelled-embedding count is used.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalHingeSupply

open Finset SignedHinge F0Geometric TypedApplicationLinks

universe u_V

section Support

variable {V : Type*} [Fintype V] [DecidableEq V]

                                                                     
                                              
                                                               
       
                                                                                            
                                                   
       

                                   
                                                                                 
                                                     
                                                                                
                         
                                                                         

end Support

section Injectivity

variable {V : Type*} [DecidableEq V]

                                                       
                                                                            
                                                         
                                     
                                                                      
                                                                                      
            

                                                       
                                                                            
                                                         
                                                 
                                                                      
                                                                                      
            

                                                             
                                                                            
                                    
                                                                                     
                                                                               
                                                                               
                                                        
                                             

end Injectivity

section Roots

variable {V : Type*} [DecidableEq V]

                                                                                         
         
                                                                                    
                                                
                                                                  
                                          
                                     
                                                                                    
                                 
            
                                                                       
                                 
                                                       
                                                            
                                                               
                                                                                              
              
                                                                         
                                                                         
                                           
                                    
                                            
         

end Roots

section Candidates

variable {V : Type*} [Fintype V] [DecidableEq V]

                                                                                                
                                                                                      
                                            
                                                         

                                                                                      
                                                             
                                                                                      
                                                                                     
                 
                                                                    
                      
                                        
                                                                     
                                                                                  
                                                            
                                        
                                                    
          

end Candidates

section Producer

variable {V : Type*} [Fintype V] [DecidableEq V]

                                                                                          
                                                                                       
                                                                                
                                                                             
                                                                                  
                                                                        
           
                      
                                                                
                                                      
                                              
                         
                                             
                                      
                                                      
                                                                                 
                               
                                                                          
                                       
                                                                                  
                                         
                                                                                 
                                               
                                                                               
                                                   
              
                                                                                           
                                                                           
                      
                                          
                                                        
              
                                                                                           
                                                                                            
                                                                                 
                                               
                                                            
              
                                                                                
                                        
                                                                  
                                          
              
                                                           
                                                              
                                                              
                                                                       
                                           
                                                                                   
                         
                                                                   
                                     
                                                                                     
                       
                                           
                                                                                          
            
                                                        
             
                                                                      
            
                                                           
                                          
                                                                          
                                 
                                              
                                                                  
                                          
                                                                    
                                       
            
             
                                            

                                                                                             
                                                                                      
                                                                                       
                                                           
                                                                         
                                               
                                                  
                                              
                               
                         
                                  
                                                                                        
                           
          

end Producer

end PartitionedTriangleAbsorption.PhysicalHingeSupply

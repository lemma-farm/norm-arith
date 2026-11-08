/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassReserveStage65.Main

/-! # Survival of the reserve's hinge supply under a bounded-degree deletion ledger

The count of `Main` is a count of actual physical edge sets inside the reserve. Here an
arbitrary edge set `D` (the *deletion ledger*) of maximum degree at most `δ n` is removed
from the reserve **after** the reserve has been chosen. A hinge `hingeEdges u v w z x y` is
destroyed only if one of its seven edges lies in `D`; the destroyed pairs `(x, y)` are covered
by seven sets, each of size at most `n · δ n`:

* `uy ∈ D`, `yw ∈ D`, `yz ∈ D`: `y` is a `D`-neighbour of `u`, `w` or `z`;
* `vx ∈ D`, `xw ∈ D`, `xz ∈ D`: `x` is a `D`-neighbour of `v`, `w` or `z`;
* `xy ∈ D`: at most `∑ₓ deg_D x ≤ n · δ n` pairs.

Hence at least `γ² ρ⁷ n² / 32 - 7 δ n²` distinct six-vertex hinges survive inside `X \ D`,
for every original root pair, every labelling constant on fibres and every family `F`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassReserveStage65

open Finset BernoulliBlocks ClassAwareHingesStage64 PhysicalHingeSupply SignedHinge

variable {V : Type*} [Fintype V] [DecidableEq V]

                             
                                                                                       

                                                    
                                                            
                                                       
              
                                                                             
             
                    
                                
                                   
             
                       

                                                                                       
                                
                                                                               

                                                                       
                                                                    
                                                                                     
                                                                                            

                                                                             
                                                                                  
                                              
                                                         
                                                                                  
               
                                                        
         
         
                                   
                                   
                                   
                                   
         

                                                                                            
                                                                    
                         
                                                    
                                                                         
           
                                           
                                                                            
                                                                         
           
                                                     
                                                                            
                                                                                     
                                                                     
                                      
                                                        
                                   
                      
                                                          
                                                        
                              
                                                                          
                                                                                      
                                                         
                                                                          
                                                                                         
                                                                          
                                                                    
                                                                          
                                               
                                                                         
                           
                                                                          
                                                
                                                                                         
                                                                                   
                                                                                   
                                                                 
                                           
                                                                                     
                                                                                     
                                                                                     
                                                                   
                     
           
                       
                                               

                 
                                             
                                                                                              
                                                                  
                                                                
                                                     
                                        
                                                                   
                                                     
                                                                                            
                                                                            
                                                                                      
                                              
                                                                             
                                                      
                                                      
                                                                    
                                                                   
                         
                                            
                                            
                               
                                                       
                                                             
                                                            
                                                             
                                                        
                                                                     
                                                  
                                                                                   
                   
                                   
                                                                                          
                                                                                   
                                                                               
                                                                            
                
                                           
                                                       
                                                     
                
                                                                            
                           
                                                                      
                                            
                          
                            
                                                
                                                               
                                                                                    
                                  
                                                                         
                                           
                               
                                                                          
                                                                                
                              
                                                                                          
                                        
                                                                                            
                                                         
                                                           
          

universe u

                                                                                   
                                                                                            
                                                                                          
                                                                                 
                                                                                        
                   
                                                                         
                                                                    
                                                            
                                          
                                                                                       
                                                                       
                                                              
                                                                                    
                                                                                
                             
                                                                                              
                                       
                                                                                     
                                                      
                
                                 
                                           
                                     
               
                                         
                   
                  
                                                              
                                                            
           
                            
                                                        
              
                                        
                                                                                          

end PartitionedTriangleAbsorption.ClassReserveStage65

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedLoadCounterexample
public import PartitionedTriangleAbsorption.TypedLoadReserveObstruction

/-! # Task B validity gate: typed load preparation for F0

* `F0SeedOnlyBoost` is the proposed intermediate target in its seed-only form:
  `b` and the input tolerance `ε` are chosen from `C` and `α` only, then for
  every precision `τ` a threshold `N`, and every graph with a `C`-regular
  `ε`-almost F0 seed which is `α`-anti-edgeful carries capped nonnegative
  weights with `τ`-precise loads. It is **false** (`not_F0SeedOnlyBoost`).
* `F0_balance_necessary` and `F0_face_necessary` give the two missing
  hypotheses, each at the precision `τ` itself.
* `F0BalancedBoostTarget` adds them (with a slack `κ` allowed to depend on
  `τ`). It is **not proved** here: it is the remaining OPEN bridge. Transferring
  its hypotheses from `G` to `J = G - (A ∪ X)` is also OPEN; the necessary
  conditions on the deletion are `reserve_balance_of_near_loads`,
  `deletion_face_of_near_loads` and `not_both_preparable`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedLoadPreparation

open Finset TypedLoadNecessity TypedLoadFamilies TypedApplicationLinks TypedLoadCounterexample

                                                         
                             
                            
                                                        
                                                                    
                                                                                    
                                                                    
                           
                                                                       
                                                           

                                                        
                                                     
         
                                                                    
                                                           
                          
                                              
                                          
               

variable {V : Type*} [Fintype V] [DecidableEq V]

                                   
                                                                  
                                                          
                                 
            
                                                                                    
                                           
                          

                                                        
                                                                                     
                                           
                                                                 
                                                                                             
                                                                     
                                                                                
                                 
                                            
                                                                      
                                                               
           

                   
                                                                          
                                                                    
                                 
            
                       
                                                                      
                                                         
                                                               
                                                                                            
                          
             
                           
                                                                                        
                   
                   
                           
                                                                                        
                   
                   
             
                                                                 
                                                                         
               
                     
            
                                                                         
               
                     
            
                                                                      
                                                     
                                                                      

                                                                              
                                                                   
                                    
                                                                                  
                                                                                       
                                                                 
                                                                 
                                     
                                                                            
                                                                                          
                                 
                                            
                                                                        
                                                               
           

                                                                           
                                                                           
                                                                            
                                                         
                                   
                            
                                                                         
                                                                    
                                                                                    
                                                                    
                                                                 
                                        
                                                                           
                               
                           
                                                                       
                                                           

end PartitionedTriangleAbsorption.TypedLoadPreparation

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F0ParallelObstruction
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Conditional F0 boost from a bounded balanced right inverse (intermediate)

This is a **conditional reduction**, not a producer. It isolates exactly what
is missing after `F0ParallelObstruction`: if the F0 copy-edge incidence map of
`J` has a right inverse on the F0-balanced edge functions whose output per copy
is at most `K/n` times the input sup norm (`HasBoundedBalancedInverse`), then
the seed, anti-edgefulness and `κ`-balance produce nonnegative weights `≤ b/n`
with every load within `τ` of one, with `b, ε` depending only on `C, K` and not
on `τ`.

The hypothesis is a linear-algebraic property of the actual copy system of `J`,
not a statement about the desired weights; but it is strong. The parallel
example fails it for every fixed `K` (`fam_not_boundedBalancedInverse`), and
deriving it on `J = G - (A ∪ X)` from geometric hypotheses on `G` is OPEN.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0RigidBoost

open Finset TypedNibble TypedLoadNecessity TypedLoadFamilies TypedApplicationLinks
  TypedLoadCounterexample TypedLoadPreparation F0ParallelObstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

                                                                                
                                                                                       

                                                                                
                                                                                
                                                                     
                                                                                      
                     
                                                                       
                                            
                                                                         
                                                         

                                   
                                                                        
                                 
            
                                                                                        
                             
               
                           
                    

                                   
                                                                    
                                 

                                                        
                                       
                                                                                            
                 
                             

                                                                                             
            
        

                       
                                                                                     
                                                                                         
                                                           
                                                              
           
                                                                  
           
                                                                   
                                                
                                                           
                     
                                                    
                                                      
                                                
                                                                               
                                       
                                                                                    
                                           
                   
           

                                                                    
                                                                              
                                                                       
                                                                        
                                                                         
                                                                    
                                                                                    
                                                                    
                                                                 
                                        
                                         
                           
                                                                       
                                                                 
                                 
                                                                             
                                         
                                  
                                
                                    
                                           
                                           
                                           
                                                                                   
                       
                                                                 
                                            
                                                                      
                                           
                                       
                                                                   
                                                               
                                               
                                   
                                                      
                                                 
                                 
           
                                                
                                                       
          
                              
                                                            
                                                                      
             
                                                        
                                            
              
                          
                                                                     
                                                                  
                                          
                                         
              
                      
                   
                                        
                 
                       
                            
                                          
                                                       
                                                              
                                                     
                                                
                                       
                                                                     
                                             
                                                                             
                                               
                         
          
                                
              
        
                                                                         
                                                             
                           
                                                
                                                      
                
                
          
                  
                            
                                                                   
                
          
                                           
                                              
               
                                                  
               
                            
                                                      
             
                            
                                  
                                                          
                      
          
                    
                                        

                                                                                 
                                                                                 
                                                                                
                                                      
                                                             
                                                   
                                                                              
                                                                                   
                                        
                              
                                   
                                                                                 
                                   
                                              
                                    
                              
             
                                                                                      
                                     
                                
                                                    
                                                         
                   
                                                    
                                                                                      
                     
                                       
                                                                                  
                                                    
                                                                             
                                                                            
                         
                                                                   
                                    

end PartitionedTriangleAbsorption.F0RigidBoost

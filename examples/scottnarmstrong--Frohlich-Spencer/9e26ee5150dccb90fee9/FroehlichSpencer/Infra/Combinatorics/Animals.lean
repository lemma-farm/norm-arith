/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import FroehlichSpencer.Infra.Lattice.Neighbors

/-!
# Lattice animals: connected vertex sets containing a vertex

In a locally finite graph with degrees at most `Δ`, the connected vertex sets of cardinality `n`
containing a fixed vertex `x` form a finite family of cardinality at most `Δ ^ (2 * (n - 1))`:
each such set is the vertex set of a walk of length `2 * (n - 1)` starting at `x`. The bound is
instantiated for the nearest-neighbour graph on `ℤ^ν`, which has degree `2 * ν`.
-/

@[expose] public section

namespace FroehlichSpencer.Infra

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

                 
                                                                     
                                                                                        
                      
                                                     
                                                           

                 
                                                                                         
                                                          
                  
                                        
                
           
                     
                                                                  
                                                                        
                                             
                                                                          
                                  
                                                                           
                           
                                         
                                             

                 
                                                                               
                                                             
           
                  
                              
                         
                                                           
                                                                              
                            

                 
                                                                            
                                                                                 
                                                                 
                                                            
           
                  
              
                                          
             
                                                                 
               
                            
                         
               
                                                                            
                 
                                    
                     
                                                          
             
                                  
                                                
                             

                                                                                               
                                                          
                                                                                    
                              
           
                                                                                  
                                               
              
                               
                         
                          

                 
                                                                    
                                                                                         
                                                                                 
           
                  
           
                     
                                              
                                           
                                         
                
                         
                                    
                                                                              
                                                                                                   
                                                 
                                                                                        
                             
                                                                                          
                                                                                                
                                    
                     
                                                                      
                                                                                            
                                                       
                                                     
                                         
                    
                                      
                                  
                                                                        
                                                                                        
                          
                           
                                                         
                                                                       
                                                                
                                                               
                                                                            
                                    
                         
                                
                                                                            
                                                                           
                                                                                     
           
                                                         
                                                                                            
                         
                 
                            
                      
                   
                        
               
                            
                                   
                                        
                                                                                
                                                                      
                                                                        
                                   
                                                                          
                                                                              
                                                          
                                 
                                            

                                                                         
                                                                                       
           
              
           
                                                
                        
                                         
             
                            
                                                                   
                            
                                                                             
                                
                           
                                                              

                                                                                            
                                                                                  
                                                

                                                                      
                                                                                   
                

                                                                                              
                                                  
           
              
           
                                  
                                                            
                                                
                                           
               
             
                                                                                     
                
                                                    
                                                                               
                                  
                             
                                             
                                          
                                                                 
                                                      
                                          

                                                                                                   
def latticeGraph (ν : ℕ) : SimpleGraph (Fin ν → ℤ) where
  Adj x y := ‖Lattice.latticeCast x - Lattice.latticeCast y‖ = 1
  symm := ⟨fun x y h => by rwa [Lattice.norm_latticeCast_sub_comm]⟩
  loopless := ⟨fun x h => by simp at h⟩

                                                    
                                                                                     
         

noncomputable instance (ν : ℕ) : (latticeGraph ν).LocallyFinite := fun x =>
  ((Lattice.exists_nearestNeighbors_finset x).choose.finite_toSet.subset fun y hy =>
    ((Lattice.exists_nearestNeighbors_finset x).choose_spec.1 y).2 hy).fintype

                                                                                             
           
                                      
                                              
                                                             
         
                                             
                                                                 
        
                                                                

                                                                      
                                                                    
                                                                            

end FroehlichSpencer.Infra

end

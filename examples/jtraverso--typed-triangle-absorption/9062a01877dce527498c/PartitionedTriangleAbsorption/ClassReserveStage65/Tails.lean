/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootQueryReserveStage59

/-! # Marker and cross-edge lower tails for one physical edge sampling

All statements use one measure `μ` on `Sym2 V → Bool` with mutually independent
coordinate events of probability `ρ`.

* `marker_lower_tail`: for a candidate set `C` disjoint from a root set `R`, a candidate `c`
  is *marked* when every edge `s(r, c)`, `r ∈ R`, is sampled. The blocks
  `starEdges R c` are pairwise disjoint (every block edge has exactly one non-root endpoint,
  namely `c`), so the marker events are mutually independent; this geometry is proved, via
  `RootQueryReserveStage59.starEdges_disjoint`, not assumed.
* `cross_lower_tail`: for disjoint vertex sets `A`, `B`, the pairs `(a, b) ∈ A × B` give
  distinct physical coordinates `s(a, b)`, so the number of sampled cross pairs is a sum of
  `|A||B|` independent Bernoulli(`ρ`) indicators.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassReserveStage65

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks RootQueryReserveStage59

variable {V : Type*} [Fintype V] [DecidableEq V]

                                                                                 
                                                             
                                               

                                               
                                                                         
                                                 

                   
                                                                        
                                                                                
                                     
                                                                                 
             
                
                          
                           
                

                                                                 
                               
                                                                      
                                                                 
           
                                                      
                                                                                            
                       
     

                             
                                                                                
                                                                         
                                                        
                                                             
                                                                      
                                                     
           
                                    
                                                                              
                       
                                                                                              
                 
                                                                            
                                    
                                                        
                                                                                 
                                                       
           
                                                                            
                                                      
                                                    
                                     
                                                                                  
                                           
                                                       
                  
                                          
            
                                       
                               
          

                                   
                                                                       
                                     
                                      
                                                                                                 
           
                                                    
                                  
                                                                   
                       
     

                                   
                                                               
                                                                                       
                                       
                                   
                
                                                  
                           
                                                         

                                   
                                                                  
                                                                               
                                                                         
                                                        
                                                                               
                                                                              
                                                     
           
                                                                         
                                                                                                  
                                                                   
                                          
           
                                                                 
                                                    
                                                                                        
                                                                                     
                                                                                
                                                                                   
        
                  
                                          
            
                                       
                                     
          

end PartitionedTriangleAbsorption.ClassReserveStage65

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RefinerAssembly

/-!
# An obstruction for refiners: echelon libraries are rigid

`RefinerAssembly.RefinesReserve indices B X R` asks that every integrally divisible
`L ⊆ X` selects pairwise edge-disjoint library pieces covering exactly `R ∪ L`.

This file proves a structural *necessary* condition on any such library.

Call a library **echelon** if its pieces can be ranked so that every piece `B i`
contains a *leading* edge `lead i ∈ R` that lies in no other piece of smaller or equal
rank.  This is exactly what happens when pieces are produced one at a time and each new
piece brings in a fresh remainder edge: for instance a triangle `{w, a, b}` stacked on an
existing pair `a, b` through a fresh apex `w` obtained from a single anti-edge request.

* `selection_eq_of_echelon`: in an echelon library the selection covering `R` exactly is
  unique, whatever the leftover is.
* `leftover_eq_of_echelon`: hence two refined leftovers coincide.
* `eq_empty_of_refinesReserve_echelon`: an echelon library refines only the empty leftover.
  So it cannot be a refiner of any reserve that contains a nonempty divisible subgraph.
* `stacked_triangles_echelon`: triangles stacked through fresh apices form an echelon
  library.  Consequently such triangle libraries, i.e. the libraries obtained from
  anti-edge requests alone, with empty private absorbers, never refine a reserve with a
  nonempty divisible subgraph (`eq_empty_of_refinesReserve_stacked`).

This is an obstruction to one design, not to refiners in general: a refiner must contain
pieces all of whose remainder edges are shared with other pieces (alternative
decompositions), as in the two decompositions of a hinge or of a private absorber.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RefinerObstruction

open Finset

variable {V I : Type*} [DecidableEq V]

                                                                                         
                                                                          
                                                            
                                                                              
                                                                                 
                                                             
                                                                      
                                         
                                                                  
                                 
                                                               
                                              
                                                                
                                             
                                                              
                                            

                                                                                      
                                                                              
                                                            
                                                                              
                                                                                 
                                                             
                                                                                     
                                                                      
           
               
                                      
                              
               
             
                                       
         
               
              
                   
                                                                
                      
              
                   
                                                                 
                      
                                                        
                                                           
              
                  
                          
                          
                                                                                              
                                
                        
                                                                    
                                                           
                                              
                                    
                                        
                                                                                       
                   
                                        
                                                                                       
                                             

                                                            
                                                                             
                                                            
                                                                              
                                                                                 
                                                                      
                                                             
                                                                                     
                                                                               
                                                                                               
                                                          
           
                                                    
       
             
            
                                                   
                                       
                                             
             
            
                                                       
                                       
                                              
             

variable {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}

                                                                                         
                                                                                            
                                                                                         
                                                
                                                                           
                                      
                                                                              
                                                                                 
                                                                             
                                               
                                                           
                                                      
                                                                      
                                                                                               

                                                                              
                                                          
                                                   
                      

                                                       
                                                                                                
                                                               
             

                                                                                       
                                                                                              
                                                        
                                                                                     
                                    
                                                                     
                                           
                                                                          
                                         
                                                                                 
                                                                  
                        
               
                                                                        

                                                                                        
                                                                                            
                                                                                     
                                                       
                                                                               
                                                               
                                                                    
                                                           
                                    
                                         
                                                                     
                                         
                                                                             
                                                                                 
                                                                      
                                                 

end PartitionedTriangleAbsorption.RefinerObstruction


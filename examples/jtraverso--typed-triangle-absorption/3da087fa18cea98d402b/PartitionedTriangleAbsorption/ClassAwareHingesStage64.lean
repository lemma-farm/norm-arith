/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Supply

/-! # Physical hinges from class-aware fibres, without universal root queries

The graph is complete between distinct structural classes. Labels are constant
on these classes. A hinge uses new vertices in the classes of its shared edge;
no common-neighbour condition for arbitrary four, five or six roots is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassAwareHingesStage64

open Finset PhysicalHingeSupply SignedHinge

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj]

                                                                                  

                 
                                                 
                                           
                                           
                                                                       
                                                     
                                               
                                                  
                                                         
                                             
                                                                             
           
                                
                                
                 
                                                 
                                                             
                                                
              
                             
                                                
              
                             
                                                     
                                 
                                                             
                                                     
              
                                        
                                  
                                  
                                                                                
                                             
                                               
                                                                                
                                                                                
                                                                                
                                                                                
                                                                                       
                                                                    
                                                                                   
                                                         
                                                            
              
                                                                     
                        
                                                                        
                                   
               
                                                            
                                                               
                                                              
                                       
                                                                             
                         
                                                                         
                        
                                                
                                              
                                              
                                                                                     

                                                 
                                           
                                                   
                                                     
                                                            
                               
           
                      
                                                                
                                                      
                                                 
                                            
                                                  
                                             
                                                                             
                                   
                                                                   
                                                                   
                     
                                             
                                                                          
                                       
                           
          
                                                                                        

end PartitionedTriangleAbsorption.ClassAwareHingesStage64

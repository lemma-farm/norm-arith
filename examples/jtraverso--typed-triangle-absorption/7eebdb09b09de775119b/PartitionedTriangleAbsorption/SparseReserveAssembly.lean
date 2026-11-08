/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Stage15

/-! # Transporting physical reserve queries to the typed graph interface

One query is a pair of distinct roots and the third part of an allowed type.
The cherry events and the graph cardinality below describe the same outcome.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SparseReserveAssembly

open Finset BernoulliBlocks AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def Query (p : V → Fin t) (F : Finset (Multiset (Fin t))) :=
  {q : V × V × Fin t // q.1 ≠ q.2.1 ∧
    ({p q.1, p q.2.1, q.2.2} : Multiset (Fin t)) ∈ F}

noncomputable instance queryFintype (p : V → Fin t) (F : Finset (Multiset (Fin t))) :
    Fintype (Query p F) := by
  classical
  unfold Query
  infer_instance

                                                                       
                                                           
           
                                                             
                                                                   
                                                                                         

                                                                      
                                                               
                                                       
                                                                                
                           
                           
                                                                  
                                                                                        
                                                         
           
            
                         
                                                              
                                                             
                                                               
                                                                         
                                                                      
                         
           
                                   
                                                                  
               
                                                                       
                                                                                        
                                                                
                                                                   
                                                                                      
                 
                     
           
                              
                        

open MeasureTheory ProbabilityTheory

                                                                 
                                                   
                                       
                                                              
                                                          
                                                    
                                                        
                     
                                       
                                                                        
                                                                          
                                                                     
                                                      
           
                                                                           
                                                           
                                              
                                                          
                                      
                                                                  
                       
                                                       
                                                                                 
                                                    
                  
                                         
                                          
                                                                        
                                                                          
                                                                     
                                  
                                                                        
                                                                          
                                                                     
              
                                                         
                        
             
                                                                          
                                                                        
           

                                                                             
                                                                              
                                                                                
                                                   
                                                     
                                                              
                                                                              
                                                                                      
                                             
                                             
                                                                             
           
                                                                             
                                    
                                               
                                                
                                                                
                                               
                                                                          
                                                                            
                                                                     
                               
                                                         
                                                             
                                                  
           
                
              
                                            
                                                                       
                                                                          
                                                                                   
                                    
                                    
                             
                                                         
                                                                    
                                            
                                                                                           
                                                            
           
                                         
                                       
                                                                                
                                         

                                                                          
                                                                           
                                                                      
                                                   
                                                     
                                                              
                                                            
                                             
                                             
                                             
                                                                             
                                                                 
                                                                            
                                                          
                                               
                                                
               
                           
                                                                           
                                                                                             
                      
           
                                 

end PartitionedTriangleAbsorption.SparseReserveAssembly

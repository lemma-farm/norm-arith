/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PositiveTargetBridgeStage96
public import PartitionedTriangleAbsorption.TripleCutPartitionStage94

/-! # Cutting the partition selected from nonnegative type coefficients

The slot equivalence produces the actual list consumed by `cut_partition`.
No token partition, physical triangle decomposition or terminal trace is an
input. Catalytic cleanup is deliberately not claimed here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SelectedTripleCutStage98

open Finset ColouredHub TargetTripleSelectionStage95 TripleCutStage94
  TypedTransformer AntiEdgeSelection CatalystInsertionStage89 PhysicalMovesStage86

variable {t : ℕ} {V : Type*} [DecidableEq V]

/-- Three slots read as one target triple, retaining repeated corner labels. -/
noncomputable def target {F : Finset (Multiset (Fin t))}
    {c : Multiset (Fin t) → ℕ} {Y : Finset (Sym2 V)}
    (f : Slots F c ≃ Y) (w : Tri F c → Fin 3 → Fin t) (x : Tri F c) :
    TargetTriple V t :=
  ⟨(f (x, 0)).val, (f (x, 1)).val, (f (x, 2)).val, w x 0, w x 1, w x 2⟩

                                                   
                                                    
                                                                     
                                         
           
       
                                                                         
                                  
             
                            
                    
                    
                    
                   
                        

                       
                                                    
                                                                    
                                                  
                                                                              
                                                                 
                                                                           
           
                                                               
                                                                     
                   
                                         
                                         
                                         
                              

                                                                               
                                                         
                                                    
                                                                                     
           
                                                         

                       
                                                     
                                                                    
                                                  
                                                                                
                                                       
           
            
                                          
                                

                                                        
                                                    
                                                       
                                                                      
           
                
                        
                                                                           
                                                  
                                                                                   

                                                   
                                                    
                                                                             
                                                                       
           
                   
               
                   
                                                                               
                      

                                                     
                                                    
                                                       
                                   
           
                           
       
                                                               
                                          

                                                                      
                                                              
                                                              
                              
                                                               
                                   
                               
                                                         
                                                   
           
                                                     
                                      
                                    
                                                
                                             
                                                          

variable [Fintype V]

                                                                               
                                                                             
                                                                            
                                                         
                                                            
                                                   
                                                               
                                                                  
                              
                                                               
                                                                 
                                                                    
                                 
                                                            
                                                        
                                                 
                                                
                                                                                             
                                                                            
                                                                                   
                                                                      
                                                                   
                                                                           
                                                                 
                                                                               
         
         

                                                                          
                                                                                    
                                                                            
                                                         
                                                            
                                                   
                                                               
                                                                  
                              
                                                                 
                                                                 
                                                                    
                                 
                                                            
                                                        
                                                 
                                                
                                                                                             
                                                                            
                                                                                
                                                     
                                                                           

                                                                          
                                                   
                                                                    
                                                    
                                         
          

                                                                             
                                                                             
                                                                             
                                                      
                                                         
                                                            
                                            
                                      
                                                               
                                  
                                                           
                                                                     
                                                             
                                                               
                                                         
                                                     
                                             
                                                 
                                                                            
                                                          
                                                       
                                                                                       
                                                                                         
                                                                           
                                                                                  
                                                  
                                                                                  
                                                           
                                                                                         
                              
                                               
                                                  
                                     
         
                                                                                   
                                                         
                            
                                                                                             
                                                                                                
                                  
                                                                              
                                                                
         
                                                                                  
                                                                                   
                                                                           
                                                             
                                                                        
                                                                                           
                                                  
                                          
                                                       
                                                                                
                       
         
         
         
         
                                  
                                      
                
                                           
                                      

end PartitionedTriangleAbsorption.SelectedTripleCutStage98

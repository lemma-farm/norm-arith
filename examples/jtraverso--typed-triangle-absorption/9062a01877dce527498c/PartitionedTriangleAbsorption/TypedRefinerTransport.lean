/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerCharge

/-! # Charge transport lower bound for every typed refiner

Fix any edge set `S` (a "region"). If a refiner selects pairwise edge-disjoint pieces of
zero charge covering `R ∪ L`, then the charge of `(R ∪ L) ∩ S` is carried entirely by the
selected pieces that meet both `S` and its complement. Each such piece carries at most
`M·K` charge. Hence a region in which two divisible leftovers differ in charge by `D`
forces at least `D / (2MK)` library pieces crossing the region boundary. This holds for any
library, any remainder `R`, and any physical or abstract realization: it is a necessary
condition, not a construction.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerTransport

open Finset TypedRefinerCharge

variable {V I : Type*} [DecidableEq V] {t : ℕ}

/-- `E` meets both the region `S` and its complement. -/
def Crosses (S E : Finset (Sym2 V)) : Prop := (E ∩ S).Nonempty ∧ (E \ S).Nonempty

instance (S E : Finset (Sym2 V)) : Decidable (Crosses S E) := by
  unfold Crosses; infer_instance

                                          
                                                                       
                                           
                                         

                                                                           
                                                                         
                                
                     
                                                                            
                     
                        
                          
                        
                
                  
                                                
                    
                  
                 

                                                                               
                                                                     
                                                                  
                                                                                     
                                  
                                                                           
                                                                  
                                                    
                                                                    
                       
                                                                   
                                                     
                                     
                  
       
                                                        

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

                                                                                        
                                                              
                                                                               
                                                                 
                                                                          
                                                                           
                                                 
                                           
                                                                   
                                                                          
                                                   
                                                                                     
                                                                        
                                                                            
                              
                                                               
                                        
                                             
                                                                                
                         
                                                 
                                                                               
                                                                
                                          
                                                 
                                                                              
                                                                 

                                                                                            
                                                                                             
                                                                                    
                                                                 
                                                                          
                        
                                                                           
                                                 
                                           
                                                                     
                                           
                                                 
                                                     
                                                                                                
              
                                  
                                                                                         
                                                                                
                                                                                
                        
                        
                                                            
                                              
                                                     
                                                  
                                                          
                
          

                                                                                            
                                                                                             
                                                                           
                                                                                        
                                                                 
                                                                          
                        
                                                 
                                           
                                                                     
                                         
                                                       
                                                    
                                                                          
            
                                                                                                
          

end PartitionedTriangleAbsorption.TypedRefinerTransport

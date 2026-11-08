/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedPaddingProducer

/-! # Uniformly bounded choices of lattice coefficients

For fixed types and a bound on the number of edges, only finitely many edge vectors occur.
Choose one integral representation of each representable vector, then take the maximum of
their negative masses. The bound precedes the vertex type, partition, and input piece.
It does not bound every possible coefficient witness and supplies no explicit growth rate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedBoundedCoefficients

open Finset TypedLatticePadding TypedPaddingProducer

variable {t : ℕ}

def negativeMass (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ) : ℕ :=
  ∑ τ ∈ F, (-c τ).toNat

                                                                                    
                                                  
                                                                 
                                                                                    
                                                                          
           
                             
                                                 
                                                                        
                                                
           
                                                                               
                                              
                                      
                           
                                                                   
                                                                                

                                                                        
                                                                                  
                                                                         
           
                                   
              
                                       
                            
                                       
                                               
                                                              
                               

                                                                                           
                                                                      
                                                                             
                                                                                
                                                                                    
                                         
                                                                       
                                     
                                                       
                                                                       
                                                        
              
                                                        
                                                          

                                                                                    
                                                                                       
                                                                 
                                                                                
                                                                                             
                                                         
                                                                
                                            
                                       
                                       
                    
                   
                                   

                                                                                      
                                                                                   
                                       
                                                               
                                                 
                                                                                
                                                             
                                       
                                 
                              
                                                  
                                               
                                                      
                                                                     
                                             
                                                      
                                       
                                       
                                       
                                     
                                                                       
                                                                             

end PartitionedTriangleAbsorption.TypedBoundedCoefficients

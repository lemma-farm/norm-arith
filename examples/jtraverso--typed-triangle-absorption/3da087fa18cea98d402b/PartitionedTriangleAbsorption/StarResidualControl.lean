/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FinitePackingRepair

/-! # The star-wise obligation missing from cardinality-only rounding

This module does not assert a new nibble theorem. It proves the deterministic
degree adapter and a finite simultaneous-outcome lemma for supplied moments.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StarResidualControl

open Finset

variable {V : Type*} [DecidableEq V]

def star (B : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  B.filter (fun e => v ∈ e)

                                                                               
                                                        
                                                                         
                                                      
         
                                           
         
                                                      
         
                                           
         
             
                                     

                                                                                
                                                                      
                                                                                 
             
             
                                                                                      
                                            
                  
                                                
            
             
                                                                                      
                                            
                  
                                          
            

                                                                                  
                                                                            
                                                                       
                                                                               
      
                                 
                                                           
                                                                      
                                                     
                                                                    
                                    
                  
                                                                                 
                                                    
          

                       
                                                                              
                                                                 
                                                  
                                         
                                                          
                                                 
               
                     
           
               

                                                                                    
                                                              
                                                          
                             
                                                                      
                                         
                                                   
                                        
                                                                                      

                                                                       
                                                                             
                                            
                                         
                                         
                                                        
                                                    
                                 
           
              
                
                                                 
           
                          
                                          
                                                        
                                                                                 
                                                           
        
                                                                
                                          
                                                                       
          

                                                                      
                                                                            
                                                     
                                                        
                                         
                                             
                                            
                                                   
                                      
                                                         
                                                               
           

end PartitionedTriangleAbsorption.StarResidualControl

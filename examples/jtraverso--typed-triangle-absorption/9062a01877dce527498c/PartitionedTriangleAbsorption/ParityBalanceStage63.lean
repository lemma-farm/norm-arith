/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.LocalCycleTransportStage62
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Algebraic core of the five-root parity/balance certificate

These are coordinate identities and scalar bounds. The global physical
producer with the improved constant is not asserted by this module.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ParityBalanceStage63

open LocalCycleTransportStage62
open scoped BigOperators

def rect {V : Type*} (e : V → V → ℤ) (u v x y : V) : ℤ :=
  e u x - e u y - e v x + e v y

                                                                        
                    
                                                                 
                 
      

                                                                        
                         
                                                                 
            
      

                                                  
                                                                
                                                
                                                 
                                                      
                                           
                                  
                                                                    
                                                         
                                              
                                                                  
             
      

                                           
                                     
                    
                                   
                                   
                                                            
         
                                   
                                   
                               
                                                             
         

                                                   
                                                        
                                  
       

                                      
                                                            
                                    
       

end PartitionedTriangleAbsorption.ParityBalanceStage63

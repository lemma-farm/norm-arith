/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Ring.Parity

/-! # Exact nonnegative coefficient tests for the typed vertex links

These are universal arithmetic equivalences, not finite searches and not
global graph decompositions. The three systems are identified with the
actual F0--F3 link generators in a separate module.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedLinkArithmetic

                                                              

def Triangle (x y z : ℕ) : Prop :=
  ∃ a b c : ℕ, x = a + b ∧ y = a + c ∧ z = b + c

                              
                                                          

                                                                       
             
                           
         
                       
                                         

                                  
                                                                                  
             
                                   
         
                              
                                                                  
         

                              
                                                                            
             
                                      
         
                                    
                       
                                                      
                                   
                                                  
                                                                  

                                                                             
                                                     
                                   
                                                      
               
       

                                                                        
                                                           
                                                                
               
       

                                                                                       
                                                                                        
               
       

end PartitionedTriangleAbsorption.TypedLinkArithmetic

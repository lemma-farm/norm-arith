/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupGenerator
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Complex exponential rescaling of a semigroup

Multiplication by `exp (t z)` shifts the full generator by `z I`, without changing its domain.
This is used to construct the Laplace resolvent from an exponentially decaying semigroup.
-/

open Set

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

                                                                        
                                                                    
                                            
                      
                    
         
                                                                   
                                                                         
                    
                                                                                  
                           
                                                                        
                                                                                    
                            

       
                                                                             
                                                                 

       
                                                                        
         
      

                                                        
                                                              
         
                                                                     
               

                                                                 
                                                                    
                                                                
                                              
                                  
      

                                                                         
                                                                 
                                        
                                                       
                                                                        
                                                                         
                            
                                                               
                                 
                                                                                                 
                                
                
              
                                                                   
                    

                                                                                          
                                                                               
                                                                              
             
           
                                
                                                                                                    
           
                                                     

end

end C0Semigroup

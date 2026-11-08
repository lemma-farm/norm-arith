/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Semigroup.Generator
import MarkovProcess.Semigroup.OrbitContinuity
import Mathlib.Analysis.ODE.Gronwall

/-!
# The generator determines the semigroup

Two strongly continuous contraction semigroups with the same generator domain and the same
generator on it are equal (`ext_of_generator`).

The proof interpolates between the two evolutions: for a vector `f` of the common domain and a
fixed time `t`, the path `s ↦ S (t - s) (T s f)` on `[0, t]` is continuous and has right
derivative zero, because

`S (t - s - h) (T (s + h) f) - S (t - s) (T s f)
    = S (t - s - h) ((T h - 1) (T s f) - (S h - 1) (T s f))`,

and the two difference quotients on the right converge to the common value of the generators at
`T s f`.  Grönwall's inequality then makes the path constant, and its two endpoints are `S t f`
and `T t f`.  Density of the generator domain extends the identity to the whole space.
-/

open Filter Set Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S T : StronglyContinuousContractionSemigroup E)

                                                                                              
                                 
                                                  
                                                   

                                                       
                                                                                      

                                                          
                                         
                             
                                                                        
                                      

                                                    
                                                         
                                                                      

                                                    
                                                         
                                                                      

                                                                                  
                                              
                                                  
                                                                                
                                                
                                                                               
                                                              
                                                     
                                                         
                                                             
                                                                       
                                                                                
                                                    
                                     
                                    
                                                                             
                                                                              
                          
                                                                           
                                                                           
                             
                                            
                          
                                                                  
                               
                                                                               
                                                                                     
              
                                                        
                                                                                         
                                              
                                                                                 
                                
                                                                                
          
                                                                                              
                                
                                                                             
                                                                  
          
                                                                  
                                 
                                                              
                                                                    
                                                                                              
                  
                                                                                            
                                                     
                                         
                                        
         
                                                                              
                                                                                 
            
                                     
                                               
                  
                           

variable [CompleteSpace E]

                                                                                               
                                                                              
                                                                       
                                                                                
                                                  
               
                                                                                  
                
                                                                        
                                                                      
                                                              
                                                                              
                 
                                                                                
                  
                                             
                                    
                                                                                         
                     
                                                              
                                  
                                                                                       
            
                    

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

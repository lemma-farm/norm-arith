/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.FiniteTime.FiniteProductCoordinateNormalForm

/-!
# Normalizing finite coordinate products

This file groups every factor of a `CoordinateProductTerm (Fin n) alpha` by its coordinate.
The normalized representation is a function into `Option C₀(alpha, ℝ)`: an active coordinate
contains the single product of all its original factors, while an inactive coordinate is `none`.

Using `none` is essential because `C₀(alpha, ℝ)` generally has no constant-one element.  Scalar
evaluation interprets inactivity as `1 : ℝ`, but the normalization itself never constructs a
spurious `1 : C₀(alpha, ℝ)`.  The resulting evaluation identity is suitable for backward kernel
recursions that branch only over active coordinates.

This is purely algebraic finite-product infrastructure: it involves no measure and no kernel.
-/

open scoped CompactlySupported ZeroAtInfty BigOperators

namespace MarkovProcess.PiContinuousMap

variable {n : ℕ} {alpha : Type*} [TopologicalSpace alpha]

                                                                                   
                                                                                      
                  
                          

                                                                                              
                                                                         
                                  
                                    
                                                                                
                  

                                                                                             
                                                            
             
                 

                                                                     
                                                             
                                             
                                                  
            
                      
             
                                              
                                                                              
                                                         

                                                           
                                           
                                                                                       
              
                                                                        
                 

                                                                                        
                                             
                                              
                                                                 
                                            
                                                                                 
                        
                                                                               
                                                                
                        
                                                                            
                        
             
                                                            
                        
                                           
                                            
                                                               
                                                                                  
                                                                                
                
                            
                 
                                                                                   
                                                            
                                                                          
                                     
                                          
                                                          
                                       

                                                             
                                                                                 
                                                                           

       
                                                                         
                 
                                                                                        
                                                                             

                                                                  
                                                                       
                                                       
                                          
                                                      
                                                                 
                        

                                                                                       
                                                              
                                                                   
                                         
                                                                                   
                                                  
                                           


end MarkovProcess.PiContinuousMap

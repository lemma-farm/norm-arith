-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.

module

public import Homogenization.Sobolev.Foundations.CubeReflection.Reflections
public import Homogenization.Sobolev.Foundations.CubeReflection.Derivatives
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib

@[expose] public section

namespace Homogenization

open Homogenization
open scoped BigOperators

/-!
# Single-face even reflection: definitions and per-line calculus

Global (on all of `ℝ^d`) even reflection of a function across the face
`{x_i = a}`, its candidate gradient (sign-flipped in direction `i` on the
reflected side), the geometric fact that the reflection commutes with coordinate
insertion, and the one-dimensional derivatives of the direct and reflected line
functions.  These feed the Fubini assembly in `FaceReflection`.
-/

noncomputable section

variable {d : ℕ}

                                                                       
                                  
                                                                  
                                                                 

                                                                                  
                                                                      
                                                                   
            
                                               
                                          
                                                           

                                                                                 
                                                              
                                                                       
                         
                                                                               
          
                                
                                
                 
                                                
                                           

                                                                                     
                                                                             
                                                                               
                                                            
                                                         
            
            
                                  
             
                                               
                                                  
                                                                      
           
                                                                                      

                                                                          
                 
                                                                      
                          
                                                                   
                            
                                                                 
                                                    
                                                                       
                    

                                                                               
                                                               
                                                                      
                                             
                                                          
                                                                                      

                                                                        
                                                                       
                                                                              
                                                       
                                                                     
                                                                  
                                           

                                                                                  
                                                                           
                                                             
                                                        
                                                                    
                                                                   
                           
                                                                        
                                                    
                      
                                                          
                                                  
                                                                  
                                                                     
                                                                   
                 
                                                    

                                                                         
                                 
                                                                                   
                                                                       
                          
                                                                       
                                                                                    
                                                                                  
                                                         

end

end Homogenization

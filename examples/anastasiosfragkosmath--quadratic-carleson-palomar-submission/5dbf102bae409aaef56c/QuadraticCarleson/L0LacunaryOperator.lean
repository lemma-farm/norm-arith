/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.SchwartzModularOperator

/-!
# The lacunary quadratic Carleson operator on the paper's full test domain

For a bounded, compactly supported measurable input, every positive symmetric
truncation is an ordinary integral.  We take the `limsup` of their norms along
the canonical cofinal sequence `epsilon_m = 1 / (m + 1)`, then the supremum
over dyadic modulations.  This gives an everywhere-defined measurable
extended-nonnegative representative without inserting an arbitrary value when
a pointwise principal value is unavailable.

Whenever the symmetric principal value exists, the `limsup` equals its norm.
In particular, the operator agrees pointwise with the distributionally defined
operator on every Schwartz function.
-/

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

namespace QuadraticCarleson

set_option autoImplicit false

                                                          
                                                     
                   

                                                                           
                             
            

                                      
                                                                   
                                  
                         
                                                                 
                                                 
                                                                 

                                                                      
                                             
                                                               
                
                                                                   

                                           
                                               
                                                                 
                                                         
                                                               
                                       
                                                                     
                
            
                                                  
                                                              

                                              
                                               
                                                                 
                                                 
                                                                                    

                                                                           
                                                              
                                          
                                                       
                                                                         

                                           
                                       
                                                            
                                 
                                                         

                                                                       
                                             
                                      
                                                            

                                                                 
                                                    
                                   
                                                              

                                                                                
                                                                
                                      
                                                            

                                                                        
                              
                                                     
                                                     
                                                        
                                                                      
                         
                                                                                 
                                                            
                      
                                                                                   
                                       
                         
                                                                
                                             
                                                            
                          

                                                
                                  
                                                  
                                                                              
                                                                    
                                                     
                                                          

                                                                           
                                                   
                                                                
                                                                      
                                                 
                                                                      
         
          
                                                                            

                                                    
                                                                
                                                             
                                     
                                                    

end QuadraticCarleson

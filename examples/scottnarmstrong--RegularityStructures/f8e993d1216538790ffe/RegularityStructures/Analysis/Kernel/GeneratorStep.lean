/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorBridge

/-!
# The derivative of `v ↦ ∫ q_v(z - y) φ(y) dy` after integration by parts

For `φ` smooth with compact support and `v > 0`,
`∫ (∂_v q_v)(z - y) φ(y) dy = ∫ q_v(z - y) (L φ)(y) dy`, where `∂_v q_v = L q_v` pointwise
(`parabolicTimeDeriv_eq`) and the derivatives of `L` are moved onto `φ` by `D_d^n` integration by
parts (`integral_iterate_dirDeriv_mul`).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

                                                                                                   
                                                                              
                                                                              
                           
                                                                  
                                                                              

                                                                                         
                                                      
                                                                                  
                                                                                           
                                                                                 

                                                                                     
                                                                           
                                             
                                                                   
                                        
                                                              
                                            
                                           
                                                        
                                                      
                                                                     
                  
                                                             
                                               
                         
                                                 
                                                               
                                                                                 
                                                                                                     
                 
                                                               
                                                                      
                                                                                                     
                                                          
                                                    
                                                                          
                                                                     
                
                                                                            
              
                                                     
                                                                                                  
                                          
                                                                                        
           
                                                       
                                                                     
                                                  
                                                                     
                                                                                     
                                          
                                                                           
           
                                                               
                                                                             
                                                                                      
                                        
                                             
        
                  
                                                              
                                                            
                                  
                                                           
                                               

end RegularityStructures

end

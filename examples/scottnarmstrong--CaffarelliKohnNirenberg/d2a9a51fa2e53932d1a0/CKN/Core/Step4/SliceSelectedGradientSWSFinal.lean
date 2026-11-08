-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientSliceCZ
import CKN.Core.Step4.SliceSelectedGradientSWSUnconditional

/-!
# Display (3.5) with the explicit Calderón–Zygmund endpoint constant

The preceding slice theorem takes the weak-gradient construction as an explicit
`hP1` input.  The concrete extension theorem supplies exactly that input at
`czGradientOperatorConstant`, so this module exposes the resulting
solution-level statement without an analytic Calderón–Zygmund premise.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

                                                                          
                                                                      
                                                                      
                    
                                                         
                                           
                 
                                      
                                                                    
                                                        
                               
                                                            
                                             
                                                                     
                                                            
                                                            
                                                      
                                                              
                                              
                                             
                                                       
                                                              
                                              
                                                                        
                                                          
                                                          
                                                    
                                    
                                                             
                                                           
                                                    
                                    
                                                                  
                                                        
                                               
                                              
                                                             
                                                            
                                                                   
                                                             
                               
                                                        
                                                   
                                                  
                                                              
                                                  
                        
                                                          
                                               
                                            
                                                         
                                                                         
                                                 
                                                                           
                                                           
                                                     
                                                         
                                                      
                                 
                                                                             
                                                           
                                                                      
                                                                                 
                                
                                                   
                                                                       
              
                                          
                                                                         
                        
                                                     
                                      
                                                       
                                                                                  
                                  
                                                       
                                                     
                                                               
                    
                                                                
                                                                               
                                                                                
                             

end CKN.Core.Step4

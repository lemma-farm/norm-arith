-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientOriginCellInstanceSource
import CKN.Core.Step4.PressureGradientOriginCellInstancePressure
import CKN.Core.Step4.SliceSelectedGradientSWSFinal
import CKN.Core.Step4.SliceSelectedGradientInputs
import CKN.Pressure.CZP1Closer

/-!
# Spatial pressure gradients from suitability

The local slice estimate `eq:pressure-gradient-morrey` applies to the centred
tensor source constructed from a suitable weak solution. Spatial gluing
then produces weak derivatives on the whole origin ball for almost every
time in the solution interval, as required by `prop:bootstrap`.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

                                                                            
                                                                             
                                             
                                      
                                                                    
                                                        
                                                            
                                             
                                                                       
                                                  
                        
                                                          
                                               
                                            
                                                         
                                                                         
                                                     
                                                                           
                                
                                           
                                               
                                                                              
                                                              
                                                                    
                                                          
                                               
                                              
                                                                  
                                      
                        
                                                 
                                                                           
                                                     
                                                                    
                                                                     
                                               
                                                   
           
                                                                                           
                                                            
                             
                                                                                  
                                                                             
                                                         
                                                                         
                                      
                                        
                              

                                                                        
                                                                        
                                              
                                       
                                        
                                                                    
                                                        
                                                            
                                                                          
                                  
                                                         
                                                            
                                                                                 
                                                                                 
                                                                           
                       
                                                                                                      
                                  
                                         

end CKN.Core.Step4

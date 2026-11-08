-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientOriginCellInstanceSource
import CKN.Foundation.Sobolev.WeakGradientGluingTBounds
import CKN.Core.Step4.PressureGradientOriginCellInstancePressure
import CKN.Core.Step4.SliceSelectedGradientSWSFinal
import CKN.Core.Step4.SliceSelectedGradientInputs
import CKN.Pressure.CZP1Closer

/-!
# Quantitative slice gradients from suitability

The complete majorant in `eq:pressure-gradient-morrey` is retained when
constructing the local pressure gradient on one interior cylinder.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

                                                        
                                                          
                               
                                                                    
                                                        
                                                               
                                                                     
                                
                                                                    
                                                                            
                                              
                                             
                                                                                   
                                                              
                                                                     
                                                   
                                          
                                                                            
                                                                 
                         
                                                                      
                                            

                                                                            
                                                                                         
                                                   
                                      
                                                                    
                                                        
                                                            
                                             
                                                                       
                                                  
                        
                                                          
                                               
                                            
                                                         
                                                                         
                                                 
                                                                           
                                                         
                                                              
                                                                           
                                
                                           
                                               
                                                                              
                                                              
                                                                    
                                                          
                                               
                                              
                                                                  
                                      
                        
                                                 
                                                                           
                                                     
                                                                    
                                                                     
                                               
                                                   
           
                                                                                           
                                                            
                             
                                                                                  
                                                                             
                                                         
                                                                         
                 

end CKN.Core.Step4

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.Bounds

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic

/-! The convolution variables are written explicitly so that the causal heat
kernel and its spatial derivatives have one common interface. -/

def pointSub (w v : ParabolicPoint) : ParabolicPoint :=
  (w.1 - v.1, w.2 - v.2)

                                                     
                               

                                                                        
                                                     

                                          
                                                                
                                        
                                                      

                                                                          
                                                                        
                               
                            
                                                               
                       

                                                                        
                 
                                                                                   
                                   
                            
                                                                      
                       

                                                                  
                        
               
                                                             
                        

                                                               
                                                              
                                                  
                                                        
                                                            
                             
                                                                         
                                              
                                          
                          
                                                           
                          
            
                                                                               
                                                                 
              

                                                                          
                        
                                                 
                                                             
                                 
                             
                                                                         
                                                  
                                         
                                                        
                                          
                                                             
                            
            
                                             
                                                             
              

                                                       
                                               
                                                 
                                                                  
                               
                             
                                                              
                                         
                                                           
                                          
                             
                                                                        
                                                       
            
                                             
                                                                    
              


end CKN.Core.HeatPotential

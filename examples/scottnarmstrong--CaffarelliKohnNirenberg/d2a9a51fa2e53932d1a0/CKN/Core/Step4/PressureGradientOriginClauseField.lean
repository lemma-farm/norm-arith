-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientOriginClauseGlue
                                                            
import CKN.Core.Step4.PressureGradientOriginClausePairing

/-!
# The pressure-gradient field on the origin carrier

Display `eq:pressure-gradient-morrey` selects, for almost every time of the
solution interval, a weak spatial gradient of the pressure slice on a ball
around the origin, together with its `L^{6/5}` bound on a smaller ball.  The
one-sided estimate `prop:bootstrap` consumes a single space-time field with
three properties: joint measurability on the carrier, integrability on every
compactly interior box, and the space-time integration-by-parts identity
against test functions supported in the carrier.

This module performs that passage.  The selection is made on each member of a
compact exhaustion of the time interval and the resulting fields are glued;
the field is then cut off outside the spatial ball of the carrier, which
changes neither the pairing identity, since the test functions vanish there,
nor the slice bounds.  The output also records the identification of the field
with every slice weak gradient, which is what pins it almost everywhere.
-/

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

                                                                               
                    
                                                                 
                                                   
                                                                                         
                                              

                                                                               
                                                                              
                                                                             
                                                                         
                                                                             
                                                                             
                   
                                                   
                                            
                                                                    
                                                        
                          
                                                            
                                                                              
                                                       
                                                                     
                                                             
                                                                              
                                            
                                                           
                                                               
                                                                              
                                                                 
                                 
                                                  
                                                          
                                                           
                                                 
                                                                                
                                       
                                                                  
                                                  
                                                            
                                                  
                                                              
                                                               
                                                                                
                                                                                
                                              
                                                                   
                                                               
                                                                              
           
                                                             
                                            
                                                
                                                         
                                                             
                                                  
                                                                                     
                                                                     
                                                                                      
                                                                            
                                                                                  
                                                                               
                             
              
                                 
                                                    
                                                                      
                                                 
                                                               
                                                                                
                                                                             
                                                                                 
                                                    
                                                   
                                                   
                                                                            
                                                     
           
                                                  
                                                     
                                                                              
         
                                           
                                    
                           
                                                 
                                   
                                                                                     
                                                                      
                                       
                
                                    
                                                                                      
              
                                     
                                                        
                                                           
           
                              
                                                                         
                               
              
                                
                                                                       
                                                             
                                                                              
                                                                                 
           
                                                
                                                     
                                                                                     
              
                            
                                                       
                                                                 
                                                                
           
                                                    
                                     
                                          
             
                                                                                       
              
                                               
                                                
              
                                         
         
                         
                                                                                   
                                  
                                                             
                       
                                                         
                                                                                          
                                                                                          
                                                         
                                                                         
                                                  
             
                                         
                                
                                                                           
                                                     
                                                                   
                                                               
                                                                    
                                                                   
                                                                   
                                                                                       
                                  
                                                                   
                                                                                
                                                
                                                   
                        
                                               
                                                 
                                                                  
                                     
                      
                                                      
                                           
                                               
                           
                        
                                         
                                                                  
                
                                           
                                                                       
                                                                            
                                             
                                                    
                                   
                                          
                     
                                          
                   
                                                            
                                                 
                                                                                
                                                                                       
                                                                    
               
                                                                 
                  
                                                           
                               
                         
                                           
                                                                            

end CKN.Core.Step4

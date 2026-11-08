-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientOneSided

/-!
# The space-time weak pressure gradient on a whole time interval

The measurable selection of a space-time weak spatial derivative from
slice-wise weak derivatives is carried out on a product box whose time factor
carries an integrable datum.  The time set of a suitable weak solution is only
an open interval, so the datum need not be integrable there; the selection is
therefore made on each member of a countable increasing family of time windows
and the resulting fields are assembled into a single one.

The assembled field is unambiguous because the slice-wise weak derivative is
unique almost everywhere on the inner spatial set: two selections made on
overlapping windows agree with the same slice derivative at almost every time.
This module records the gluing construction and the geometric facts about the
unit domain hypothesis of the one-sided pressure estimate.
-/

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

                                                                            
                                              
                                                                     
                                                                                
                                                                             
                                                                    
             
              
                                                 
                                                                                     
                     
                              
                       
              
                                                    
                                                                                     
                                                   
                       
                     
              
                        
                       

                                                                             
                                                                                
                                            
                          
                                                        
                                               
                          
       
                                                         
                                                          
                              

                                                                             
                                                        
                                                                        
                                    
                                                         
                                                                  
                   
                                                     
                                                                              
                  
                             
              
                                    
                                      
                   
                                      
             

                        
                                                                       
                                                    
                                                                         
                         
                                                             

                                                                                    
                                                                                     
                                                  
                                                   
                                              
           
                                      
                                     
                 
                                  
                          
                                             
                                                                    
                   

                                                      
                                                                                   
                                                
                                          
           
                                                        
                                                                        

                                                                             
                                                                             
                                                                         
                                                                            
            
                                                          
                                                          
                                                                            
                           
                                                       
                          
                                                
                                                        
                                      
                                                        
                             
                                                  
                                                 
                                        
                                                         
                                                       
                                                                                 
                                
                                                                       
                                                        
                                                     
           
                                              
                                                               
                                                                                      
                                                                             
                                                                    
                                 
           
              
                           
                                                 
                                                     
                                                     
                                        
                                                         
                                                        
                                                                        
                                
                                                                       
                                                             
           
                                   
                                                                        
                                                               
                          
                                              
                                                                             
                                                
           
                                                                                 
              
                                                      
                                                         
                                      
                                                       
                                                                                  
                                      
           
                                                                               
                                                          
                                                                                         
              
                                                         
            
                     
                                                         
                                                                 
                                         
           
                                               
                                  
                                                                                   
                          
                                              
                                                     
                                                             
                                                                           
                                                                         
                       
                               
                                                  
                                                                                        
                                                           
                                 
                                     
                                                                     
             
                                  
              
                                                             
              
                                

end CKN.Core.Step4

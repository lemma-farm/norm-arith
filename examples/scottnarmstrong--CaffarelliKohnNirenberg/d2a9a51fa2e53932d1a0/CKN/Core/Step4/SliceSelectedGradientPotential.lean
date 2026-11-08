-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.Potentials
import CKN.Pressure.LeibnizLaplacian

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

/-! The pressure-gradient section of the paper controls `∇p` through the weak pairing
against a compactly supported test function, as in display (3.5).  The Newtonian
derivative potential of a source field is the kernel representation of that weak
gradient.  This file records the integrability input that display (3.5) assumes, the
local integrability of a finite sum of such potentials, and the passage from a
per-coordinate Calderón–Zygmund bound to the corresponding bound for the potential of
a vector-valued source. -/

                                                                            
                                                                                 
                                                                                   
                                                                                 
         
                                                                       
                                                                                    
                             
                                 
                                                                              
              
                                             
                                         
                                               

                                                                                     
                                                                                      
                                                                           
                                                                                     
                         
                                                                  
                                                                                  
                                                             
                     
                                                                                            
                           
                                                                                            
                 
                                                                     
                                                                               
                                                                         
                 
                                                                               
                        
                  

                                                                                      
                                                                                  
                                                                                      
                                                                                   
                                                                               
                                                                                 
                                                                       
                                                           
              
                                        
                                                                         
                        
                                                     
                                      
                                                       
                                                                                  
                                  
                                                       
                                                                              
                     
                                                                                  
                                                             
                      
                                                   
                                    
                                                     
                                                                                
                                                        
                                                     
                             
                                                                                         
           
                                                                                             
                                                                            
                                                         
                                                   
                                                                                             
                                                      
                             
                                                         
                                                                                             
                         
                                                           
                                                                  
                                                                       
                                                                          
                                                                     
                                                                                  
                    
                
                                  
                  
                                             
                  
              
                                
                                            
                                                   
                                                                              
                                                            
                    
                                                                                            
                                                          
                                                                            
                                                  
                                                  
                                                                                       
                 
                                                                         
                                                              
                                                                                            
                                                                                       
                                                                                  
                                          
                                                                         
                                                                                           
                                    
                                                                        
        
                                                                              
                               
                                                                                 
                                      
                                   
                                 
                               
                                                                               
                                   
                                                                                  
                                       
                                                                 
                                          
                                       
                                          
                                                                                       
                                            
                   
                                   
                                 
                               
                                      
                                 
                                                                       
                           
                                                                                       
                                                                
                                             
                                                                 
                                                                              
                                       
                     
        
                                                      
                                                 
                                                                     
                                               
                                   
                                                                               
                                                    
                               
                                                   
                                                                                  
                               
                               
                                                                                          
               
                                             

end CKN.Core.Step4

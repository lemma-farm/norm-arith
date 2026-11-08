/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.FirstNoise
public import Critical2DKPZ.Collision.SpatialRenewal
import Mathlib

/-! # Arrival kernels before the terminal disorder coordinate

The parameter `n` counts the weighted steps before the last, unweighted step.
Thus the arrival time is `a + n + 1`, and all disorder in the arrival kernel is
strictly earlier than that time.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.Blocks

                                                                                  
                                                                          
                                                      

                                                                   
                                                                           
                              
                                                                  
                              
                                                                 
                                                                       
                                     
      

                                                                     
                                                                                   
                                    
                                                                                
                                             
                                              
                      


                                                                        
                                                                            
                                                             
                                                                                      
                 

                                                                          
                                                                           
                                                           
                                           
                                                                            
                                           
                                                                

                                                                        
                                                                              
                                         
                                                                             
                                                               
                                                                             

                                                                 
                                                                           
                                                                                 
                                                                                   

                                               
                                                                         
                                                                       
                                                                           


                                                                                                           
                                                                                
                                                            
                               
                                                                 
                                                                    
                                                                           
                                                             
                                                              
                                                                        
                                                       
                                                                          
                                                                                
                                            
                     
                   
                             
                                                               
                                                 
                                           
                                                                 
                                                                 
                                                       
                                                               
                                                                     
                                                                    
                                      
                                                
                                          
                                

                                                                                                                                  
                                                                                  
                                                                               
                                                                        
                     
           
                                      
                                                                              
                                                                                              
                                       
                          
                                                                  
                                                                     
                                                                       
                                                                       
                                                                         
                                                                
                                                                         
                                          
                                        
                                                             
                                                   
                                                                          
                                                           
                                                   
                                                          
                                      
      
                             
                                                                                     
                                                      
                                                                           
                                      

end Critical2DKPZ.Blocks

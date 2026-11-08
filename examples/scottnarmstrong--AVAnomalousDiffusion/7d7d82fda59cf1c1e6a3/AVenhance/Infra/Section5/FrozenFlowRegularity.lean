-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Construction.StreamAdmissible
public import AVenhance.Infra.Flow.JointC1
public import AVenhance.Infra.Flow.InverseC1
public import AVenhance.Infra.Flow.SpatialC2
public import AVenhance.Infra.Flow.SpatialC3
public import AVenhance.Statements.Section4.XFlow
public import AVenhance.Statements.Section4.XFlowInv
public import AVenhance.Statements.FlowDefs.FlowIsFlow
public import Mathlib
/-! Joint first-order regularity for the §4 flow slices. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

                                             
                                    
                                                             
                                                             

                                             
                                    
                                  
                                   
                                                                        
                   

                                                                        
                                   
                                            
                                      
                                      
                                
                                                
                                 
                                  
                                                                 
                                                 
                                                          
                                                                                                 
                                 
                                                                 
                                  

                                                                             
                                                                    
                     
                            
                                                                
                                                                   
                                                                           
                  
                                                              
                                     

                                                                   
                                  
                                                    
                                         
                                
                                                
                                 
                                  
                                        
                                            
                                                                                                     

                                                           
                                     
                                                    
                                            
                                
                                                
                                 
                                  
                                        
                                            
                                                                                                     

                                                                   
                                    
                                                    
                                         
                                
                                                
                                 
                                  
                                        
                                              
                                                                                                     

                                                           
                                       
                                                    
                                            
                                
                                                
                                 
                                  
                                        
                                              
                                                                                                     

end AVenhance.Infra.Section5

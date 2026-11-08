module

                                     
public import SharpWasserstein.FlowDependence
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

/-! A measurable solution map is constructed, rather than assumed, for every
bounded globally Lipschitz drift and every continuous additive input. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace SharpWasserstein.BoundedFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {v : ℝ → E → E} {M K : ℝ≥0}

                                                                                   
                                                                          
                      

                                           
                                                                            
                                                                            

                                                                            
                                                                 
                                               
                                                               
                                                               
                                                                                       
               

                                                              
                                                               
                                                      
                                                                                  
                                                                                            
               

                                                                                  
                                                                 
                                                               
                                                        
                                
                                                       
                                                        
                                                                    
                                                 
                                                   
                                                                          
           
                                                   

                                                                                
                                                             
                                                               
                                                     
                                                             
                                                                     
                                    
           
                   
                                                                    
                                           
                                                             
                                        
                                     
                         
                                        
                                     
                          
      
                                                                 
                                                  
                                                              
                    

                                                              
                                                               
                                                     
                                                                           
                                            

                                                                      
                                                                    
                                                               
                          
                                                        
                                             
                                                     
                                               
           
                                                                   
           
                                                        
                                                                        
                                   
                                                                                                 

                                                                       
                                                                    
                                                               
                                                    
                                                                             
                                                                   
                                                       
                           
                                                                                   

end SharpWasserstein.BoundedFlow

module

public import RequestProject.Euler.BanachBackwardSequence
public import RequestProject.Euler.BanachHyperbolicGreen
public import RequestProject.Euler.BanachWeightedFixedPoint

/-! A genuine nonlinear ancient discrete orbit is constructed by a
contraction from a true C¹ map and bounded invariant splitting data.
The initial expanding coordinate is prescribed exactly, and the graph
error can be made arbitrarily small relative to that coordinate. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction ContDiff

namespace Euler2D

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]

                                               
                                                           
                                               
                                                                        
                                                       
                                                   
                                  
                                                                 
                            
                                                  
                                                        
                  
                                    
                                     
                                            
                                           
                                         
                                          
                                                 
                                                              
                                                
                                                                        
                                                                               
                                                                                
                                                               
                                                                 
                                                                                   
                      
                                     
                                                                     
                                                                               
                   
                                                                     
                                                           
                                            
                                      
                
                                                                                 
                                               
                                                             
                                                            
                                                 
                                                 
                                                      
                                                                                  
                                                             
                                                                
                                                  
                                               
                                                                 
                                                                                      
                                                                       
                                                                      
        
                                               
                                                                  
                                 
                                                                        
                                    
                                                          
           
               
                
           
                                                                       
           
                                                    
                                    
                                                          
        
                                                          
                                                                   
                                                            
                                                
                      
                                         
                              
                                                                      
                     
        
                                                                                               
                                                                       
                                          
                                                                                        
                                                    

end Euler2D

end

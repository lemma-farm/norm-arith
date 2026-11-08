module

public import RequestProject.Euler.BanachWeightedRemainder
public import Mathlib.Topology.MetricSpace.Contracting

/-! A genuine contraction constructs the weighted nonlinear orbit
sequence, with quantitative distance from its prescribed linear source. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

                                                                           
                                                         
                                                                   
                                
                                                            
                                     
                                    
                                                                       
                         
                                               
                                                        
                                                                    
                                 
                                              
                                                                  
                                                           
                                                                       
                                                                                                    
        
                                            
                                                      
                                                                                  
                                                                            
                                                      
                                                            
                      
                                                                           
                                                                                        
                                            
               
                        
              
                                        
               
                                                                          
                                     
                                                                                      
             
          
                                              
                                                                    
                                                                                         
                                                      
                                                                                           
                                                                                 
                                                 
                                                       
                                                                                                     
                                         
                                      
                                                     
          
                                              
                                              
                                                          
                                                                                    
                                                      
                                                
             
                            
                                                      
           
      
                              
                                                                              
                                                                  
                                                                           
                                                  

end Euler2D

end

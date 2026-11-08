module

public import Paper.ParisiMildDerivative
public import Paper.ParisiTestRegularity
public import Paper.HeatAdjoint

@[expose] public section


/-!
# Distributional spatial derivatives of the constructed Parisi potential

The weak gradient is verified against actual smooth compactly supported
tests.  Spatial integration by parts and absolute integrability on the
time-space product discharge the distributional identity.
-/

open Set MeasureTheory ProbabilityTheory
open scoped Topology ContDiff

namespace Paper

instance : IsLocallyFiniteMeasure parisiSpaceTime := by
  unfold parisiSpaceTime
  infer_instance

                                                         
                                                                                        
                                                                         
                                                   
                                     
            
                                        

                                                                      
                                                                  
                                                            
                                           
                                       
                                                                                   
                 
                                                                     
                                                                                       
                                                                          
                                                            
                                                              
                                                                      
                        
                                   
                                                                                     
                              
                                                              
                                                                        
                                                                        
                                                                                   
                                                                                    
                                                      
                                                                      
                                                                         
                                                               
                                                             
                                                              
                                                             
                                                              
                                                            
                                                      
                                                                  
                                                                       
               
                                 
      

end Paper

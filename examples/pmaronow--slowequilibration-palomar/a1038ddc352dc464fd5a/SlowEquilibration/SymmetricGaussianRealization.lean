-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianCovarianceRepresentation

/-! Actual centered Gaussian symmetric matrix laws admit a fixed-dimensional
linear realization under the manuscript's covariance domination on symmetric
test matrices. Symmetry is required only almost surely for the original law. -/

@[expose] public section
namespace SlowEquilibration.SymmetricGaussianRealization
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK GaussianCovarianceRepresentation
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {m : ℕ}

                                                                                                  
                                                        
                                                                                                                                                  
                                                                                                     

                                                                                            
                                 
                                                                

                                                                                    
                                              
                                        
      

                                                                  
                                                    
           
                                        

                                                              
                                                        
         
                                      
      

                                                                                           
                                                          
                                                                               
      
                                                          
                                                               
                                                       

                                                              
                                                                              
                                                                     
                                                                     
               
                                                                    
                                                        
      

                                                                                              
                                                                  
                                                          
                                                                   
                                                                                     
                                                                                         
                                                                                     
                           
                                   
                                
         
                                               
                                                                                          
                    

                                                                          
                                                                       
                                            
                                                                  
                                                                  
                        
                                                  
                                                                     
                                                                                           
                                        
                                              
                                             
                                                                                   
                                                                            
                                                 
                                       
                                                         
                                                  
           
                                          
                                                                             
                                                  
                                                                     
                          
                                                                                                  
                                                                                    
                                             

end
end SlowEquilibration.SymmetricGaussianRealization

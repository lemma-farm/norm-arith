-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDominatedEdge

/-! The actual two-sided operator norm tail follows from the proved Gaussian
upper-edge bound for a matrix and its negative. -/

@[expose] public section
namespace SlowEquilibration.GaussianSpectralNorm
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK GaussianDominatedEdge
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

                                                                         
                                                   
                                                            
                                                      
                                                                 
                                                
         
                                                                      
                                 
                                                                               
                                               
                                                            
                                                                             
                   
                         
           
                                                  
                                                                    

                                                                               
                                                 
                                                                         
                                                                                        
                                           
                                                
                                                                           
                                  
                                                                  
                                                                                           
                                                                
                                         
                                                                       
                                                          
                                                                           
                              
                                                                                          
                                                    
                                                                             
                                                       

                                                                              
                                                    
                                           
                                                                                
                                                              
                                                              
         
                                                      
                                                          
                                                        
                                        

                                                                            
                                                                      
                                                      
                                                       
                          
                                                   
                                                         
                                             
                                                    
               
                                  
             
                                                                          
                                                                    
                                                                        
                                                                 
                                                   
                                                          
              
                                                        
                      
         
                 
                                                                                          
                                           
                            
      
                                                       
                                                      
                                                                                 
                                                           

end
end SlowEquilibration.GaussianSpectralNorm

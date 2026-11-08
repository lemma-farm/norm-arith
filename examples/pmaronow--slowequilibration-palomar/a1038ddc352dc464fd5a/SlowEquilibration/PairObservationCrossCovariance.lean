-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NormalizedPairObservations
public import SlowEquilibration.SphericalTwoPointCovariance
public import SlowEquilibration.ScalarCoefficientCovariance

/-! Literal bilinear cross Gram forms of the normalized actual two-point
observations. No dimension-sized matrix norm estimate is substituted. -/
@[expose] public section
namespace SlowEquilibration.PairObservationCrossCovariance
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance ScalarCoefficientCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

                                                                     
                                         
                                                                                           
                                                      
                                                                                          
            
                                             
                    
                                    

                                                                        
                                                                     
                                                                
                                     
                      
                           
                           
                                                                                        
                                               
                                              
                                              
                                                                       
                                                                
                                                                                         
                                                                
                                                                                         
                                      
                                                              
            
                                                                                 
                                                                              
                                               
                                             
                                                         
                                                                                          
                                                             
                                                                                   
                                                          
                                                  
                                                             
                                                                        
                                                                                           
                                        
                                                             
                                                                                     
                                          
                                                                                            
                              
                                                                                 
                                             
                                                                       
                                                                               
            
           
                                                                    
      

                                                                           
                                                                     
                                                                
                                     
                      
                           
                           
                                                                                        
                                           
                                                              
                                                              
                                      
                                                              
            
                                                                                 
                                                                              
                                               
                                                  
                                                             
                                                                        
                                                                                           
                                                                                  
                                             
                                                                       
                                                                               
            
           
                                                                    
      

end
end SlowEquilibration.PairObservationCrossCovariance

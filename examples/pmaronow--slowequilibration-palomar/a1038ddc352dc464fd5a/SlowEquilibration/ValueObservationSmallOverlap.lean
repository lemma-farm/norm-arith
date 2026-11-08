-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairObservationSmallOverlap

/-! Proper value-only pair conditioning, including pure mixtures. -/
@[expose] public section
namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationCrossCovariance PairObservationNormBounds
open NormalizedObservationCoercivity GaussianObservationCoercivity GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

                                                                                       
                                   
                                                                                     
                                         

                                                                        
                                                         
                                                          
                                                                          
                                                             
                              
                                                                                           
                                           
                         
                         
                    
                        
                                             
                                             
                                                             
                                                             
                                                                           
                                         
                        
                                              
                                      
        
                                               
                          
                      
                                       
                                                             
                                                                                 
                                              
                                                     
                     
                                                                                                 
                                           
                                                
                                                
                                      
                                                                
              
                        
              
                                           
                                                                      
        
          
                          

                                                                      
                                                         
                                                          
                                                                          
                              
                                                                                  
                                           
                                                                                         
                 
                                                                                                
                      
                                                                                                    

                                                                          
                                                               
                                                                                 
                              
                                                         
                                                  
                                                                    
                                                         
                          
                                                         
                                                                                      
                                                                             
                                                    
                                                     
                       
                                       
                          
                                                           
                                      
                                                 
                                                            
                                         
                                        
                                                             
             
                                                                                                     
                                                                                                         
                                                                               
                                        
                                        
                                                 
                                                              
                                                 

end
end SlowEquilibration.PairObservationSmallOverlap

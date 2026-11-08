-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ObservationCrossBlocks
public import SlowEquilibration.PairObservationNormBounds

/-! Sharp dimension-free orders of the actual cross observation blocks,
used by the two-point Gaussian density factorization. -/
@[expose] public section
namespace SlowEquilibration.PairObservationCrossCovariance
noncomputable section
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationNormBounds
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

                                         
                                                               
                                                    
                                         
                                 
                                 
                                 
                                 
                                        
          

                                                                          
                               
                                                                                  
                                                                             

                                                                           
                                                                   
                                                                              
                                               
                                                                
                                              
                                                                                         
                 
                                                                              
                                                
                                       
                                       
                                                       
                                                                                                         
                                                              

                                                                   
                                                                            
                                                                                     
                                           
                                                                       
                
        
                                                                                                 
                                                                        
                                                     

                                                                        
                                              
                                                                              
                                                                              
                                                                                     
                              
                                                              
                                                  
                                                                                         
                 
                                                                            
                                                         
                                       
                                                               
                                                                
                                                 
                                                    
                                                                                              
                                                
                                                                                
                                                                                                
                                                                                                
                                                                                  
                                                                    

                                                                    
                                                                     
                                                                        
                                                                              
                                                          
                                                                          
                              
                                                            
                                                  
                                                                                         
                 
                                                                          
                                                   
                     
                     
                                                    
                                                    
                                                       
                        
                                                 
                                                      
                                                                                                  
                                           
                                                                                       
                                           
                                                                                              
                                                                                                      
                                                                             
                                                                            
                                                                                 
                                                                                       
                                                                    

end
end SlowEquilibration.PairObservationCrossCovariance

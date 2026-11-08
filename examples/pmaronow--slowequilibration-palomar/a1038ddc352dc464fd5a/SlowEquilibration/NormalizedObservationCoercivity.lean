-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NormalizedPairObservations
public import SlowEquilibration.GaussianObservationLowerBound
public import SlowEquilibration.SphericalScoreDensity

/-! Genuine dimension-independent one-point observation coercivity. The
score constant is chosen from a fixed one-dimensional actual field; the
normalized Gram is literally identical in every spatial dimension. -/
@[expose] public section
namespace SlowEquilibration.NormalizedObservationCoercivity
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity SphericalPairRegression
open SphericalSequentialRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

                                                                    
                                                             
                                                                                 
          

                                                                               
                                                            
                                                                  
                                                 
                                                                                                           
                               
                                                                   
                                                    
                                               
                                                 
                                         
                  

                                                                                     
                                                            
                                                                                           
                                                                                         
                                         
                                                                       
                                                          
                                                    
                                                                                                       
      

                                                                       
                                                                         
                                       
                                                           
                                       
                                                                                                 
                                                   
                                                                            
                                                                                                           
                  
                   
                                                                                     
            

                                                                    
                                                          
                                                                                  
                                                                                                          
         
                                     
                                                                                                
                                                   
                                                                                                         

                                                                                 
                                                                          
                                                           
                                            
           
             
                                      
                                                                        
                                      
                                                                         

                                                                         
                                       
                                                                         
                                       
                                                             
                                                              
                                 
                                                                                                             
                                                         
                  
                                                      
                                         
                                     
                             
                              
           
                                                                                                 
           
                                                                             
                                                    
                                                                                     
                                                                                           
                                                                    
              

                                                                        
                                                            
                                                                                           
                                               
                                                              
                                               
                                                 
                                         
                             

                                                                                 
                                                                          
                                                           
                                                                                    
         
                                                                        
                                                              
                                                                                
                                  

                                                                       
                                                                            
                                                                           
                                                             
                                                              
                                 
                                                                                                             
                  
                                                      
                       
                                                 
                                            
                             
                              
           
                                 
                                                                                                     
                                                               
                                                                                                   
                                                                    
           
                                                                                    
                                                    
                                                                                     
                                                                                           
                                                                                      
                                                                    
              

end
end SlowEquilibration.NormalizedObservationCoercivity

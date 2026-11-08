-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairOrthogonalJetCovariances
public import SlowEquilibration.SphericalHessianTraceCovariance
public import SlowEquilibration.ValueTangentConditioning
public import SlowEquilibration.GaussianOrthogonalRegression

/-! Actual two-point whole-disorder Gaussian observations, with separate
nonpure value/radial observations and proper value-only pure observations.
Zero-overlap nonsingularity is derived from the original tensor covariances. -/

@[expose] public section
namespace SlowEquilibration.SphericalPairRegression

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicHessianLaw
open IntrinsicGradientRegression ValueTangentConditioning GaussianRegression
open PairOrthogonalJetCovariances
open scoped RealInnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

                                                                              
                                                                
                                                          
                                                                                          
                                        

                                                                             
                                       
                                                                
                                                          
                                                                                          
                                                      

                                                                     
                                                                              
                                                      
                                           
                                                                                   
              
            
               
                                                   
             
                                                                                    
                                                       
                                         
             
                                                                          
                                                      
            
                                         
           
                                                                                               

                                                                              
                                                      
                                           
                                                                                          
              
            
                                                 
           
                                                                                      
            
                                         
           
                                                                                         

                                                                            
                                                        
                                                                          
                                                        
                                                                       
                                                           
                                                                             
                                   
                                                                                             
                                                

                                                                                          
                                                        
                                                        
                                                                      
                                                                           
                            
                                                    
                                                   
           
                  
           
                                                            
                                              
                               
         
                                                                                  

                                                                           
                                                            
                                                             
                                                                              
                                                                     
                                                          
                                            
           
                                                          
                                                          
                 
                                                                    

                                                             
                                                                              
                                                                     
                                                                        
                                            
           
                                                          
                                                          
                 
                                                                    

                                                                            
                                                          
                                                
                                                                          
                                                                          
                                                                          
                                                                           
                                                            
                                                 
         
                                   
                
                                        
                                                                                              
                                        
                                                                                              

                                                                          
                                                                    
                                                                    
                                                                                   
                                                                      
                           
                                                         
                                                                                 
                                                       
                                  
                                                                                                                        
                                                                                                                        
                                                     
                                                                                  
                                                

                                                                            
                                              
                                                                    
                                                 
                                                                      
                           
                                                         
                                                                                 
                                                       
                                  
                                                                                                                           
                                                                                                                           
                                                     
                                                                                  
                                                

end
end SlowEquilibration.SphericalPairRegression

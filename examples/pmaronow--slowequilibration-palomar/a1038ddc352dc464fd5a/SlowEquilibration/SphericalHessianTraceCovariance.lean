-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedIntrinsicHessian
public import SlowEquilibration.GaussianRegressionCovariance

/-! Literal trace covariance of the actual full tangent Hessian and its true
covariance contraction under canonical full-coefficient Gaussian regression. -/

@[expose] public section
namespace SlowEquilibration.SphericalHessianTraceCovariance

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicHessianLaw
open GaussianRegressionCovariance SymmetricGaussianCovariance GOEAsymptotics
open OAI.CriticalSK
open scoped BigOperators Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

                                                                     
                                                                        
                                                                    
                                                                                           
                                                                                                              
                                     
                                                                                           
                                                                         

                                                                                    
                                                                      
                                                                                  
                                        

                                                                                
                                                        
                                                                             
           
                                      
                                     

                                                                    
                                                                
                                                          
                                                                  
                                                                   
                                
                                                                                                

                                                                          
                                                                        
                                                              
                                                                
                                               
                                                         
                                                                    
                                                                                        
                                                                         
                                                                                                       
                                                                    
                                                              
                               
                                                                    
                                                                              
                                 
                             
                                                    
                                                       
                                                            
                                                              
                                                                                    
                                                                  
                     
                            
            
                     
                            
            
             
      

                                                                     
                                                    
                                                                  
                                                                
                                               
                                                         
                                                                    
                                                    
                                                                            
                                                                         
                                                                                                            
                                       
            
                                                                                                 
                                                                                     
                                                                                                              
                               
         
                                                            
                                                                    
             
                                                                  
                                                                  
                                                                                                  
                                   
                                                                
                                                                           
                                                                           
                                           
                                                                
                                                                                            
                                                                         
                                                                   
           
                                                                                                       

                                                                          
                                                                            
                                                     
                                                                        
                                                                          
                                      
                                                                        
                                                                
                                               
                                                         
                                                                    
                                                                                               
                                                                      
                                                                                   
                                                                   

end
end SlowEquilibration.SphericalHessianTraceCovariance

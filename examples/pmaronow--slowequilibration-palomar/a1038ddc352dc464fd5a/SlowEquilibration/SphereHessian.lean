-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalChartGeometry
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual intrinsic Hessian and its coefficient/chart determinant

The intrinsic Hessian is the tangent projection of the actual derivative of
the spherical gradient. Its extrinsic derivative formula is proved directly.
-/

@[expose] public section

namespace SlowEquilibration.SphereHessian

open MeasureTheory ProbabilityTheory Set Function Metric InnerProductSpace
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphericalChartGeometry SlowEquilibration.GaussianLocalCoordinates
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace Topology ENNReal

noncomputable section

variable {N n : ℕ}

                                                                          
                                                             
                                    

                                                                          
                                                                           
                                                                                               
                                                
                                                                     

                                                                           
                                                             
                                               
                                                                              
          
                                                                                    

                                                                          
                                                                   
                                                                             
                                                                                     
                                         
                                                                                                     
                                                                
                           
                                            
                                                          
                                                                             
                      
                                                                                
                                 
                                                        
                                                    
                                                             
                                            
                                
                                        
                                                                                        
                                                 
                                                        
                                                                              
                                                                             
                                                                         

                                                                           
                                                                               
                                             
                                                                 
                                                                     

                                                                          
                                                                             
                                                                                     
                        
                                                       
                                                   
                                                                 
                                                                           
                                               
                     
                                                    
         
                                                                           
                                                    
                                                                                   

                                                                            
                                    
                                                                                              
                                    
                                                                   
                                                  
                                                                     

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

                                                                                             
                                                           
                                                       

                                                                      
                                                                    
                                                      
                                                                                         
                                                                              
                                                                
         
                                                                                       
                         
                                                                                            
         
                                                               
                                                           
                                                             

                                                                          
                                  
                                                                        
                                                                                     
                                                                 
                                                                                
                        
         
                                                                                        
                                                             
                                                         
                                                                            
                                                                              
                                                                            

                                                                        
                                                        
                                                                                      
                                                    
                         
                                        
                                                                              

                                                                        
                                                      
                                                                 
                                                                          
                                                                     
                                                                  
                                                                
                                                                          
                                                                             
                                           
                                                          
                                                                         
                                            
                                                                           
                                                                              
                                                                      
                                                        
                                                                  
                                                                                      
                                               
                                                                                       
                            
                                     
                                           
                               
                                                                                
                               
         
                        
         
                                                                                     
                               
                                                              
                                            
     

                                                                        
                                             
                                                                                  
                                                              
                                                       
                                                   
                                         
                                                                     
                                                       
                                              
                                                                                        
                                 
           
                          
           
                                                                                       
       
                                  
                                                                         
                                   

                                                                         
                                                                       
                                                         
                                                                          
                                                                     
                                                                      
                                                                    
                                                                                               

end
end SlowEquilibration.SphereHessian

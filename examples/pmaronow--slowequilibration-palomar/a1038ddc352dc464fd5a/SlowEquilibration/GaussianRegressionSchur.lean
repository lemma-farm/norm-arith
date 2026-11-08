-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegressionCovariance
public import SlowEquilibration.GaussianOrthogonalRegression

/-! Actual residual score covariance and its Schur complement after
conditioning on a genuine finite-dimensional Gaussian observation. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

                                                            
                                         
                                      
                                                       

                                                              
                                                   
                                      
                                                                 

                                                                           
                                                                                 
                                      
                                                                              
      
                               
                                                                    
                                                                        
                                                  
                                                                             
             
           
                                                                             
                                             

                                                                        
                                                       
                                                                          
                     
                                         
                                                   
                                                              
                                                               
                                                                             
           
      
                                                                                  
                                            
                                                                                  
            
                                                  
                                                      

                               
                                                                         
                                                                  
                                       
         
                                 
                                                    
                                                                                     
                                                                        

end
end SlowEquilibration.GaussianRegression

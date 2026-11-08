-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegressionSchur
public import SlowEquilibration.GaussianResidualCoercivity

/-! Genuine sequential Gaussian disintegration at a specified gradient-zero
fiber, without requiring the original mark observation to be independent. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianObservationCoercivity
open scoped RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

                               
                                                                                   
                                                                 
       
                                                                 
             
            
                                    
                                    
                       
                       
                                                                                                                                       
                    
                                    
                             
                                
                    
                                 
                  
               
               

                                                                                    
                                                     
                                                                            
                                                    
                                                    
                                                                                           
                                                                          
                                                                                          
                                                                                                              
                              
                        
         
                
                                                             
                                                               
                   
             

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace G] [BorelSpace G]

                                                                      
                                                                
                                                                             
                                                           
                                                                                  
                                       
                                                                               
                                                   
                                                  
                                                    
                                                                                           
                                                                                  
                                                         
                                                           

end
end SlowEquilibration.GaussianRegression

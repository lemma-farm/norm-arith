-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairScoreCovariancePerturbation
public import SlowEquilibration.GaussianResidualCoercivity

/-! Actual uniform covariance lower bounds for both tangent gradients and
for the residual pair scores after conditioning at both gradient zeros. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function GaussianRegression
open scoped RealInnerProductSpace
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
                                                               
                                                                                 
         
                                  
                                                                                    
                                                                                          
end
end SlowEquilibration.GaussianObservationCoercivity

namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

                                                                           
                                                                               
                                                                                       
                                                                
                                                                           
                                 
                                                                    
                                                                              
                                                         
                                   
                                        
                                                                         
                                                                               
                                                                           
                         
                                                 
                                                     
                                                 
                                                      
                                                                                
                                            
                                                                                          
                                                       
                                                                    

end
end SlowEquilibration.PairObservationSmallOverlap

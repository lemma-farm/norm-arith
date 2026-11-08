-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianNonorthogonalRegression
public import SlowEquilibration.PairResidualScoreCoercivity

/-! Literal pair-gradient-zero disintegration of all original tensor
coefficients through the actual conditional score density. -/
@[expose] public section
namespace SlowEquilibration.WholeFieldRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel
open GaussianRegression GaussianObservationCoercivity
open scoped ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {N P : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

                                                                         
                                                               
                                                           
                                                           
                                                                                                  
                                                                                             
                                        
                                                                      
                                                                                   
                                                        
                                                                                      
                                                                                         
                                               
                                                                    
                                            
                                                     
                                                                 
                                                                                                
            
                                                                                         
                                                  
                                                                                      

end
end SlowEquilibration.WholeFieldRegression

namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression GaussianRegression GaussianObservationCoercivity NormalizedPairObservations
open scoped ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

                                                                          
                                                            
                                                                                       
                                                                
                                                                 
                                 
                                                                    
                                                                              
                                                              
                                                         
                                                                 
                                                             
                                                                                                
                                                                           
                    
                                                          
                                                     
                                                 
                                                      
                                                                                
                                            
                                                                                          
                                                                                       
                                                                                                     

end
end SlowEquilibration.PairObservationSmallOverlap

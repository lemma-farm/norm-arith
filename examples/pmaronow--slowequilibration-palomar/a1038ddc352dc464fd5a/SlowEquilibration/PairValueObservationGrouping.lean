-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairObservationGrouping
public import SlowEquilibration.PairScoreDisintegration

/-! Proper pure/value pair observations, without redundant radial scores. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity SphericalSequentialRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

                                                        
                                                                               
                                                    
                                                   
                                                    
                  
                                     
                                                                                                  
                                                       
                                                                                                                
                                               
                 
           
                                                        
                                            
                                                                       
                                                                 
        

                                       
                                                                                     

def normalizedValue {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    EuclideanDisorder N P →L[ℝ] ℝ := (Real.sqrt (N:ℝ))⁻¹ • valueCLM c x

                                                             
                                                                                                         

                                                                    
                                                                                     
                                                        

                                                                     
                                                                            
                                                                               

                                                                         
                              
                                                                                                     
                                                                                       
       
     

                                                                               
                                    
                                                                                                              
                                                            
         
                                                                                                                                 
                                                                                                                                                                                

end
end SlowEquilibration.NormalizedPairObservations

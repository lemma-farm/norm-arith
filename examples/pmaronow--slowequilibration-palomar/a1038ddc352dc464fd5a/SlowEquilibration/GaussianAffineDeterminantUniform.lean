module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.GaussianAffineDeterminant
public import SlowEquilibration.GaussianDominatedEdge

@[expose] public section

/-! # Uniform large-N moments of actual covariance-dominated affine determinants -/

namespace SlowEquilibration.GaussianAffineDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Set MeasureTheory ProbabilityTheory Filter
open OAI.CriticalSK GOEAsymptotics
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology
universe u

                                                          
                                         
                                                               
                                                               
                                                
                        
                                                   
                                                                                 
                                                        
                      
                                                                              
                                         

                                                                   
                                                                           
                                                                                
                                                                
                                             
                                                                      
                                                                   
                                                                        
                                        
                                                                          
                                        
                                                  
                                                                                      
                
                                                         
          

                                                                                
                      
                                                                             
                                           
                                                                      
                                                   
                                                                                     
                                                                  
            
           
        
                                                   
                                            
                                                                                        

                                                                        
                                                            
                                                                                           
                                         
                                                
                                                 
                                                                           
                                                             
                                                             
                                    
                                                                      
                                                                                          
                                                                           
                                            
                                                 
                                                                                  
                                                                   
                                                          

                                                                       
                                                          
structure NormalizedMomentBounds {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)) (k ρ M : ℝ) : Prop where
  integrable : Integrable (absoluteDet C W k) (SYK.standardGaussianMeasureOnEuclidean ι)
  expectation_pos : 0 < ∫ g, absoluteDet C W k g ∂SYK.standardGaussianMeasureOnEuclidean ι
  raw_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun g => (absoluteDet C W k g /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
    (SYK.standardGaussianMeasureOnEuclidean ι)
  clipped_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun g => (Real.exp (clippedTrace C W k ρ g) /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
    (SYK.standardGaussianMeasureOnEuclidean ι)
  ordered : ∀ r : ℝ, 0 ≤ r →
    (∫ g, (absoluteDet C W k g /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
    (∫ g, (Real.exp (clippedTrace C W k ρ g) /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι)
  bound : ∀ r : ℝ, 0 ≤ r →
    (∫ g, (Real.exp (clippedTrace C W k ρ g) /
      (∫ h, absoluteDet C W k h ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ (2:ℝ)^r*Real.exp (M*r^2)

namespace NormalizedMomentBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
  {C : GOEAsymptotics.GaussianMatrix (n+1)}
  {W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)} {k ρ M : ℝ}

                                                                               
                                
                                                                             
                                                                              
                                       

end NormalizedMomentBounds

                                                                           
                                                                          
                                                                  
                                                                                           
                                         
                                                
                                                 
                                                                           
                                                             
                                                             
                                                                                       
                                                                                    
                                            
                                                               
                                                                      
                                    
                                                    
                                                               
                                                              
                                                                                       
                                                                                        
            
                                                                                     
                                                                                                           
                                                                                            
      
                                                                      
                    

end
end SlowEquilibration.GaussianAffineDeterminant

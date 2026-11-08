module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.GaussianAffineDeterminantFinite

@[expose] public section

/-! # All-N actual affine Gaussian determinant moments -/

namespace SlowEquilibration.GaussianAffineDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Set MeasureTheory ProbabilityTheory Filter
open OAI.CriticalSK GOEAsymptotics
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology

/-- The fixed coefficient space in the genuine Gaussian covariance
factorization, allowing degenerate covariance as well. -/
abbrev CoefficientIndex (n : ℕ) := Fin (Module.finrank ℝ (GOEAsymptotics.GaussianMatrix (n+1)))

/-- Returned actual raw and clipped normalized moments, with a single
constant chosen before all ambient dimensions and matrix parameters. -/
structure UniformMomentBounds {n : ℕ}
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ (CoefficientIndex n) →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (k ρ K : ℝ) : Prop where
  integrable : Integrable (absoluteDet C W k) (SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n))
  expectation_pos : 0 < ∫ z, absoluteDet C W k z ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)
  raw_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun z => (absoluteDet C W k z /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r)
    (SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n))
  clipped_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun z => (Real.exp (clippedTrace C W k ρ z) /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r)
    (SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n))
  ordered : ∀ r : ℝ, 0 ≤ r →
    (∫ z, (absoluteDet C W k z /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r
      ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)) ≤
    (∫ z, (Real.exp (clippedTrace C W k ρ z) /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r
      ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n))
  bound : ∀ r : ℝ, 0 ≤ r →
    (∫ z, (Real.exp (clippedTrace C W k ρ z) /
      (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)))^r
      ∂SYK.standardGaussianMeasureOnEuclidean (CoefficientIndex n)) ≤ K^r*Real.exp (K*r^2)

namespace UniformMomentBounds
variable {n : ℕ} {C : GOEAsymptotics.GaussianMatrix (n+1)}
  {W : EuclideanSpace ℝ (CoefficientIndex n) →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1)} {k ρ K : ℝ}

                                                                            
                                
                                                                                                
                                                                                             
                                       
end UniformMomentBounds

                                                                         
                                                                           
                                                                   
                                                                                               
                                           
                                                 
                                                                                              
                                                             
                                                             
                                                                            
                          
                          
                                             
                                                      
                                    
                                                                    
                                                                                                  
                                       
                                                                       
                                         
                                  
                                         
                                                                      
                                                                 
                               
                                        
                       
                                                                               
                                                                                                        
              
                                                                                    
                                                                          
                                                             
                                
                                               
                                                                                              
                                                                 
                                                                 
                                             
                             
                                                     
                                                                                             
                                                                              
                                                      
                                                                         
              
                                     
                                                                 
                                                                            
                                                               

end
end SlowEquilibration.GaussianAffineDeterminant

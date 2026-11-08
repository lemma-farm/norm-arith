-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SymmetricGaussianCovariance
public import SlowEquilibration.GaussianAffineDeterminantAllDimensions

/-! Normalized determinant moments under the actual arbitrary Gaussian
matrix law satisfying the manuscript's trace covariance bound. -/

@[expose] public section
namespace SlowEquilibration.GaussianMatrixMomentLaw
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK SpectralTraceLipschitz
open SymmetricGaussianCovariance GaussianAffineDeterminant
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ}

def rawDet (C : GOEAsymptotics.GaussianMatrix (n+1)) (k : ℝ)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) : ℝ :=
  |(k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)-gaussianToMatrix (C+A)).det|

def logClipped (C : GOEAsymptotics.GaussianMatrix (n+1)) (k ρ : ℝ)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) : ℝ :=
  ∑ i, clippedLog k ρ (matrixOrderedEigenvalues (C+A) i)

                                                                           
                                 
                                                                                                
                                                                                 
               
          

                                                                                 
                                       
                              
                             
           
                                                            
                                                                                                
                             

structure MomentBounds (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1)))
    (C : GOEAsymptotics.GaussianMatrix (n+1)) (k ρ : ℝ) (bound : ℝ → ℝ) : Prop where
  integrable : Integrable (rawDet C k) μ
  expectation_pos : 0 < ∫ A, rawDet C k A ∂μ
  raw_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun A => (rawDet C k A/(∫ B, rawDet C k B ∂μ))^r) μ
  clipped_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun A => (Real.exp (logClipped C k ρ A)/(∫ B, rawDet C k B ∂μ))^r) μ
  ordered : ∀ r : ℝ, 0 ≤ r →
    (∫ A, (rawDet C k A/(∫ B, rawDet C k B ∂μ))^r ∂μ) ≤
      ∫ A, (Real.exp (logClipped C k ρ A)/(∫ B, rawDet C k B ∂μ))^r ∂μ
  upper : ∀ r : ℝ, 0 ≤ r →
    (∫ A, (Real.exp (logClipped C k ρ A)/(∫ B, rawDet C k B ∂μ))^r ∂μ) ≤ bound r

                                                                         
                                                       
                                             
                                                                      
                                                               
                             
                                                                                    
                                                                                   
                            
                                                 
                                                                                
                                                    
                                                               
                                                                                
                                                    
                                  
                                                                               
                                                    
                                                
                                                                               
                                                    
                                                
                                                                               
                                                               
                                    
                                    
                                  
                                              
                                    
                                                                              
                                                                   
       
                                                                                                                                    
                                
                                                                                                                                                      
                                
                                                     
             
                                                                                 
              
                                                                                       
                       
              
                                                                                        
                         
              
                                                                             
                                                                  
                           
              
                                                                              
                           

                                                                       
                                                                              
                                             
                                                                               
                                           
                                                                           
                                                         
                                                                          
                                                               
                                                         
                                                                         
                                                                  
                                                                    
                                                                                 
                    
                                                 
                                                                                         
                                               
                                                                                     
                                                                                                  

                                                                        
                                                                           
                                                                                 
                                         
                                                                           
                                                         
                                                                          
                                                               
                                                         
                                                                         
                                                                  
                                                                                
                                                                                  
                                               
                                                                                         
                                                                                    
                           
                                                                                     
                                                                                                  

end
end SlowEquilibration.GaussianMatrixMomentLaw

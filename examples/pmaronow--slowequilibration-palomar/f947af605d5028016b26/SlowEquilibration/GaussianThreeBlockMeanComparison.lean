-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianThreeBlockComparison

@[expose] public section

/-! Three-block Guerra comparison from the actual disorder-averaged
pair covariance. The fixed perturbation block cancels from the derivative. -/
namespace SlowEquilibration.GaussianThreeBlockComparison
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

def pairKernelExpectation (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Fin 3) (θ : ℝ) (w : EuclideanSpace ℝ ι) : ℝ :=
  ∫ z : V × V,signedKernel L label z.1 z.2
    ∂(GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w).prod
      (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w)

                                                                       
                                      
                                                                                   

theorem pairKernelExpectation_eq_coordinate_sum (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K)
    (label : ι → Fin 3) (θ : ℝ) (w : EuclideanSpace ℝ ι) :
    pairKernelExpectation ν L label θ w=
      ∑ i,covarianceSign label i*
        (GaussianSpinInterpolation.expectation ν (coordinateObservable L i) (rotatedLinear L label θ) w)^2 := by
  let G:=GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w
  let _:=GaussianSpinInterpolation.gibbsMeasure_probability ν _
    (rotatedLinear_measurable L hL label θ) (rotatedLinear_bound ν L hK hb label θ) w
  unfold pairKernelExpectation signedKernel
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (((gibbsCoordinate_memLp ν L hL hK hb label θ w i).integrable (by norm_num)).mul_prod
      ((gibbsCoordinate_memLp ν L hL hK hb label θ w i).integrable (by norm_num))).const_mul _)]
  simp only [integral_const_mul,integral_prod_mul]
  simp_rw [GaussianSpinInterpolation.integral_gibbsMeasure ν _
    (rotatedLinear_measurable L hL label θ) (rotatedLinear_bound ν L hK hb label θ)]
  simp only [pow_two]

                                                                                          
                                                            
                                             
                                 
                                                                                                   
                                                                                  
                                                                                                         
                                                                               
                                        
           
                            
                                                                                            
                                                                
                                                                                                         
                                                                 
                              
                                                                                                                   
                 
                                            
                                                          
                                                                                                 

                                                                   
                                                            
                                             
                                                                                      
                                                                        
                                                                             
                                                                                   
                                    
                                                                     
                                                                                
                                                 
                                                                               
                                                                 
                                                                                       
                                                              
                                                       
                                              
                                                                                   
                                                       
           
       
                                                                         
                                                                     
                                                                  

                                                                                            
                                                            
                                             
                                                                              
                                                                      
                                            
                                                                     
                                              
                                            
                                                                                          
                                
                                                                                                
                 
                                                            
                                                                                          
        
                                                         
                                                     
                                                                                                   
                
                                                          
                
                                                             
                       
                                                                                                    
                                                                                            
                                                                             
                                                                                               
                     
                                                                                    
                  
                     
          

end
end SlowEquilibration.GaussianThreeBlockComparison

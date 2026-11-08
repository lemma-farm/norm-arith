-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianInterpolation
public import SlowEquilibration.SphericalGuerraBound
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! # Actual quenched-pressure stability under varying temperature

The genuine Gibbs-replica derivative and spherical overlap bound give a
dimension-independent Lipschitz estimate. A fixed-temperature limit therefore
transports to convergent temperature sequences, including sequences approaching
a static endpoint from above.
-/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Nonnegative tensor coefficients control the absolute covariance at every
signed spherical overlap; no parity condition is needed. -/
theorem abs_covariancePolynomial_le_at_one {P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {r : ℝ} (hr : |r| ≤ 1) :
    |covariancePolynomial c r| ≤ covariancePolynomial c 1 := by
  unfold covariancePolynomial
  calc
    |∑ p, c p * r ^ (p : ℕ)| ≤ ∑ p, |c p * r ^ (p : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, c p * 1 ^ (p : ℕ) := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul, abs_of_nonneg (hc p), abs_pow, one_pow, mul_one]
      exact mul_le_of_le_one_right (hc p) (pow_le_one₀ (abs_nonneg _) hr)

                                                                         
                                                   
                                                              
                                                                                
                                                              
                                                    
                                   
                                                             
                                                 
                                                 
                                        
                                                                                          
                                                                                      
                                                                                 
                                                                                 
                  
                                                 
                                                                                 
                                 
                         
                                                 
                                                                
                                                                                   
                                        

                                                           
                                                          
                                 
                                           
                                                   
                                                                                          
                                                  
                                                                         
                                                                 
                          
                           
                                                     
                                                                  
                                                 
                                                             
                                        

                                                                        
                                                                              
                                  
                                                       
                                                                                   
                                                         
                                                 
                                                               
                                                   
                                                                                            
        
                                                            
                                                     
                                                                                            
                                                        
      
                                                            
                                                                       

                                                                     
                                    
                                                                   
                                                                           
                                                       
                              
                                     
                                                       
                                                         
                                                         
                                                    

                                                                        
                                                                           
             
                                                                        
                                                  
                                                                
                                
                                                                          
                                                                       
                                        
                                                                               
                                                                
                                                   
                            
         
                                                       
                                           
                                                     
                                                   
                                                          
                                                                       
                       
                              
                                                  

                                                                   
                                      
                                                          
                                         

                                                                             
                                              
                                    

                                                                           
                                                               
                                                                 
                                                                                
                                                                
                                
                                                                                    
                                                                                 
                                                                  

                                                                   
                                                                           
                                                                                  
                                  
                                                                          
                                                                                     
                       
                                                         
                                                                  
                                                            
                                                      

end
end SlowEquilibration.SphericalModel

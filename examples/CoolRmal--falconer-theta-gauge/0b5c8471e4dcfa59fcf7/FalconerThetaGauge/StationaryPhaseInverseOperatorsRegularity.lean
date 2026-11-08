/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.PolynomialDifferentialActionFinite
public import FalconerThetaGauge.PolynomialWeightedNorm
public import FalconerThetaGauge.StationaryPhaseInverseOperatorsConjugate

/-! # Actual derivative regularity of the stationary and inverse operators -/

@[expose] public section

noncomputable section

open Finset Polynomial
open scoped ContDiff

namespace FalconerThetaGauge

/-- Applying a polynomial of order `d` consumes exactly `d` input derivatives and
multiplies the amplitude bound by its literal weighted coefficient norm. -/
theorem polynomialDifferentialAction_isDerivativeRegular {G : ℝ → ℂ}
    {A M : ℝ} {K d : ℕ} (hG : IsDerivativeRegular A M (K + d) G)
    (p : Polynomial ℂ) (hp : p.natDegree ≤ d) :
    IsDerivativeRegular (A * polynomialWeightedNorm p M) M K
      (polynomialDifferentialAction p G) := by
  have hM : 0 ≤ M := by linarith [hG.one_le_scale]
  refine ⟨mul_nonneg hG.amplitude_nonneg (polynomialWeightedNorm_nonneg p hM),
    hG.one_le_scale, contDiff_polynomialDifferentialAction_of_natDegree_le hG.smooth p hp, ?_⟩
  intro m hm x
  rw [iteratedDeriv_polynomialDifferentialAction_of_natDegree_le hG.smooth p hp hm]
  calc
    _ ≤ ∑ n ∈ p.support, ‖p.coeff n * iteratedDeriv (m + n) G x‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ p.support, ‖p.coeff n‖ * (A * M ^ (m + n)) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply hG.bound
      have hnd := (le_natDegree_of_mem_supp n hn).trans hp
      omega
    _ = (A * polynomialWeightedNorm p M) * M ^ m := by
      rw [polynomialWeightedNorm, Polynomial.sum_def, mul_sum, sum_mul]
      apply sum_congr rfl
      intro n _
      rw [pow_add]
      ring

                                                                           
                                                                                       
                                                                            
                                                        
                                                                

                                                                                          
                                                                            
                                                                      
                                            

                                                                      
                                                                      
                                                                                           
                                                 
                                                       
                                                     

                                                                               
                                                                      
                                                                                           
                                                             
                                                               
                                                 
                                                              
                                                                               
                                                    

                                                                          
                                                                                                  
                                                                                         
                                                                          

                                                               
                                                                      
                                                                 
                                                   
                                                               
                                                                            
                                                               
                                             

                                                                        
                                                                      
                                                                 
                                                            
                                                                            
                                                                                
                                                                                
                                        
                                                      
                                                            
                                                               
                                                  
                                                                       

                                                                          
                                                                                        
                                                                        
              
                                                               
                                                   

                                                                              
                                                                      
                                                                                   
                                                       
                                                
                                                                 
                                                                                  
                          

                                                                               
                                                                                   
                                                       
                                                         
                                                                          
                                                                                  
                          

end FalconerThetaGauge

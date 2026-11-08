module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-!
# Positive Laplace kernels for the Kummer integral

This module develops the kernel on real parameters, independently of the series module.
Only positive integration variables and positive Laplace parameters are characterized.
-/

@[expose] public section

open Set MeasureTheory Real

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

                                                                                 
                                                        
                                                           

                                                                 
                                                          
                                       
                                                                      
                                                    

                                                                     
                                                    
                                                        
                        
                          
                                                                      
                                                                         
                                                             
                             
                        
                                                 

                                                                             
theorem one_add_rpow_le_polynomial (q : ℝ) (n : ℕ) (hqn : q ≤ (n : ℝ))
    (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ q ≤ (2 : ℝ) ^ n * (1 + t ^ n) := by
  have hbase : 1 ≤ 1 + t := by linarith only [ht]
  have hpow : (1 + t) ^ q ≤ (1 + t) ^ n := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase hqn
  apply hpow.trans
  by_cases ht1 : t ≤ 1
  · have hsmall : (1 + t) ^ n ≤ (2 : ℝ) ^ n :=
      pow_le_pow_left₀ (by linarith only [ht]) (by linarith only [ht1]) n
    exact hsmall.trans (le_mul_of_one_le_right (by positivity) (by
      have := pow_nonneg ht n
      linarith only [this]))
  · have ht1' : 1 ≤ t := (lt_of_not_ge ht1).le
    have hlarge : (1 + t) ^ n ≤ (2 * t) ^ n :=
      pow_le_pow_left₀ (by linarith only [ht]) (by linarith only [ht1']) n
    rw [mul_pow] at hlarge
    exact hlarge.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

/-- The scaled Gamma kernel is integrable for every positive shape and rate. -/
theorem integrableOn_gammaKernel (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => Real.exp (-(z * t)) * t ^ (a - 1))
      (Ioi 0) volume := by
  have hscaled : IntegrableOn
      (fun t : ℝ => Real.exp (-(z * t)) * (z * t) ^ (a - 1))
      (Ioi 0) volume := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) 0 hz).mpr
    simpa only [mul_zero] using Real.GammaIntegral_convergent ha
  have h := hscaled.const_mul (z ^ (a - 1))⁻¹
  apply IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro t ht
  change (z ^ (a - 1))⁻¹ *
    (Real.exp (-(z * t)) * (z * t) ^ (a - 1)) =
      Real.exp (-(z * t)) * t ^ (a - 1)
  rw [Real.mul_rpow hz.le ht.le]
  have hn := (Real.rpow_pos_of_pos hz (a - 1)).ne'
  field_simp

                                                              
                                                                              
                                                               
                                             
                                                                                   
                                                        
                                                                            
                  
                                                                                       
                                                                
                                                                        
                                                                     
                                             
                                                                              
                                                                
                                                           
                                            
                                      
                                                  
                                                    
            
                                 

                                                       
                                                                              
                                                           
                                                                            
                       
              
                                                
                                               
                       
                             
                                                                
                                               
                                                    

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

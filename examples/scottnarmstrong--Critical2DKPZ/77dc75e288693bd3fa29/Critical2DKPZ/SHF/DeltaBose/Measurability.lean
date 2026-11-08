/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
import Mathlib
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Measurability of the collision kernels

The scalar collision integrand, parameter integrals and nonnegative diagram series are jointly measurable. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Joint Borel measurability of the real-power operation. -/
theorem measurable_real_rpow : Measurable (fun p : ℝ × ℝ => p.1 ^ p.2) := by
  have heq : (fun p : ℝ × ℝ => p.1 ^ p.2) = fun p =>
      if p.1 = 0 then (if p.2 = 0 then 1 else 0) else
        if p.1 < 0 then Real.exp (Real.log p.1 * p.2) * Real.cos (p.2 * Real.pi)
        else Real.exp (Real.log p.1 * p.2) := by
    funext p
    split_ifs with hx hy hn
    · simp [hx, hy]
    · simp [hx, hy]
    · exact Real.rpow_def_of_neg hn _
    · exact Real.rpow_def_of_pos (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx)) _
  rw [heq]
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
  · exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      measurable_const measurable_const
  · apply Measurable.ite (measurableSet_lt measurable_fst measurable_const) <;> fun_prop

/-- The reciprocal Gamma function is continuous even at the nonpositive integers. -/
theorem continuous_inv_gamma : Continuous (fun u : ℝ => (Real.Gamma u)⁻¹) := by
  have h := Complex.continuous_re.comp
    (Complex.differentiable_one_div_Gamma.continuous.comp Complex.continuous_ofReal)
  simpa only [Function.comp_def, Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re] using h

/-- The scalar collision integrand is jointly measurable in its parameter, time and integration variable. -/
theorem measurable_scalarIntegrand :
    Measurable (fun p : (ℝ × ℝ) × ℝ => scalarIntegrand p.1.1 p.1.2 p.2) := by
  unfold scalarIntegrand
  simp only [div_eq_mul_inv]
  have hp : Measurable (fun p : (ℝ × ℝ) × ℝ => (p.1.2, p.2 - 1)) := by fun_prop
  exact ((measurable_real_rpow.comp hp).mul (by fun_prop)).mul
    (continuous_inv_gamma.measurable.comp measurable_snd)

                                                                                    
                                                                                            
                                                                           
                                              

                                                                       
                                       
                                                                                                    
                              
          

                                                                                  
                                                                 
                                                                     
                                             
                                                                                        
                                                                 

                                                 
                                                                   
                                                                          
                                               
                                                             
                                                                       
                                                                   

                                                           
                                                                  
                                                                                
                                                      
                                   
                                                                       
                                                                           
          

                                                                                    
                                                                
                                    
                                           
                                            
                                                              
                                                                    
                                                                    
                                                                
                                                                 
                   
          
                                              
                       
         
     

                                                                                      
                                                                            
                                                                                
                                                                 
                                                                         
                  
          
                                 
                                                                                    
                  
                                 
                             
                                                      
                                                                          
                                         
                                         
                                                                          
                                                                
                                                                
                                                              
                                                            
                                                             
                                                     
                                                            
                                                                                              
                                                     
                                                                             
                                          
                                                                                 
                                                                    
                                                                            
                                                                                                    
                            

                                                                    
                                                                       
                                                                      
                                                 
                                                                                         

                                                                       
                                         
                                                                      
                                                   
                     
                                                                              
                                                         
                                   
                                                                                                
                                                                              
                                              
                                                                    
                         
           
                               
             
                                    
                 

end Critical2DKPZ.DeltaBose

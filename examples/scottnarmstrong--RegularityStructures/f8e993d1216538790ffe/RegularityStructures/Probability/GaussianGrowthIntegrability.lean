/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Polynomial moments of a one-dimensional Gaussian

The Gaussian Poincare proof uses polynomial growth only as an explicit analytic hypothesis.
This file records the corresponding moment closure, using Fernique's finite-moment theorem.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace RegularityStructures

                                                       
                                                    
                                        
                                         
                                 
                                      
                                        
                     
           
                                                                              
                         
                            
                                           
                                             
                            
                        
                
                                   
                                                             
                                                   
                                                          
                                                                            
                                                                             
                          
                                                   
            
             
                                    
                                
                                               
                  
                               
                     
                          
                                        
                                         
                                                                                      
                                    

                                                            
                                                    
                                        
                                           
                                         
                                  
                                                                    

theorem integrable_gaussian_weight_of_integrable {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => f x * gaussianPDFReal 0 1 x) (volume : Measure ℝ) := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) hv] at hf
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => gaussianPDF_lt_top))] at hf
  refine hf.congr ?_
  filter_upwards [] with x
  simp [smul_eq_mul, mul_comm]

end RegularityStructures

end

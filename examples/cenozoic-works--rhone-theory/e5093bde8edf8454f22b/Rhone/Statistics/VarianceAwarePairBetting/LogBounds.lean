/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Local logarithm estimates for the one-third tuning -/

@[expose] public section

namespace Rhone.Statistics.VarianceAwarePairBetting

                                                                                         
                                                    
                                                   
                                                        
               
                                      
                                                 
                              
                                         
                                                           
                            
                            
          

theorem abs_log_one_add_upper {x : ℝ} (hx : |x| ≤ 1 / 3) :
    |Real.log (1 + x)| ≤ 3 / 2 * |x| := by
  have hab : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hab 0
  norm_num [abs_neg, sub_neg_eq_add] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - |x|)).mpr
  have hp := mul_le_mul_of_nonneg_left hx (abs_nonneg x)
  nlinarith [abs_nonneg x]

theorem log_one_add_sq_upper {x : ℝ} (hx : |x| ≤ 1 / 3) :
    Real.log (1 + x) ^ 2 ≤ 9 / 4 * x ^ 2 := by
  have h := abs_log_one_add_upper hx
  have hh := mul_self_le_mul_self (abs_nonneg _) h
  nlinarith [sq_abs (Real.log (1 + x)), sq_abs x]

end Rhone.Statistics.VarianceAwarePairBetting

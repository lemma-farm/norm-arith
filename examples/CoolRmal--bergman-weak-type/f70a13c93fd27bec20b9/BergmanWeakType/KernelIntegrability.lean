/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Kernel
public import BergmanWeakType.Measure
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Integrability of the Bergman integral formulas

For each interior output point, both kernel columns are bounded on the input disk. Consequently
their products with integrable inputs are integrable. The Bochner integrals defining the complex
projections therefore represent genuine integrable functions, and the positive outputs are finite.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

                                                                                   

                                                                        
                                                                 

/-- A fixed interior output point keeps the kernel denominator uniformly away from zero. -/
theorem kernel_denominator_norm_lower (z : ℂ) {w : ℂ} (hw : w ∈ disk) :
    1 - ‖z‖ ≤ ‖1 - z * star w‖ := by
  have hmul : ‖z * star w‖ ≤ ‖z‖ := by
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg z) ((mem_disk_iff w).mp hw).le
  calc
    1 - ‖z‖ ≤ 1 - ‖z * star w‖ := sub_le_sub_left hmul 1
    _ ≤ ‖1 - z * star w‖ := by simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) _

theorem norm_kernel_le {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    ‖kernel z w‖ ≤ (1 - ‖z‖)⁻¹ ^ 2 := by
  rw [norm_kernel]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
    (inv_anti₀ (sub_pos.mpr ((mem_disk_iff z).mp hz))
      (kernel_denominator_norm_lower z hw)) 2

theorem norm_weightedKernel_le {α : ℝ} (hα : -1 < α) {z w : ℂ}
    (hz : z ∈ disk) (hw : w ∈ disk) :
    ‖weightedKernel α z w‖ ≤ (1 - ‖z‖) ^ (-(α + 2)) := by
  rw [norm_weightedKernel]
  exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr ((mem_disk_iff z).mp hz))
    (kernel_denominator_norm_lower z hw) (by linarith)

                                                                          
                                                                     
                                                
                               
                                                                              
            
                                                                                

                                                                                        
                                            
                                                              
                                          

                                                             
                                               
                                                                  

                                                                             
                                                                 
                                                          
                                                                                         

                                                                                                   
                                                                              
                                                                          
                                                   
                                                        

                                                                                                 
                                                                       
                                                                  
                                                                          
                                                             
                                                                                

                                                                                  
                                                      
                                                               
                                                                                    

                                                                           
                                                                  
                                              
                                                                       
                                   
                                                                 

end BergmanWeakType

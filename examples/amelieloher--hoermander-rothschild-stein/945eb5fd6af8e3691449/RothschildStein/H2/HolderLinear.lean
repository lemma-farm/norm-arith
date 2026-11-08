-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderOperations
public import RothschildStein.H2.PrincipalValueLimits
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Absolute homogeneity of the auxiliary Hölder norm. -/
theorem boundedHolderNorm_smul {δ : ℝ≥0} {U : Set X} (c : ℝ) (f : X → ℝ) :
    boundedHolderNorm δ U (c • f) = ENNReal.ofReal |c| * boundedHolderNorm δ U f := by
  unfold boundedHolderNorm holderSup holderSemi
  have hs : (⨆ x : U, ENNReal.ofReal |(c • f) x|) =
      ENNReal.ofReal |c| * ⨆ x : U, ENNReal.ofReal |f x| := by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
    rw [ENNReal.mul_iSup]
  rw [hs]
  have hh : eHolderNorm δ (fun x : U => (c • f) x) =
      ENNReal.ofReal |c| * eHolderNorm δ (fun x : U => f x) := by
    have he := eHolderNorm_smul (r := δ) (f := fun x : U => f x) c
    rw [← ENNReal.ofReal_coe_nnreal] at he
    have hfun : (fun x : U => (c • f) x) = c • (fun x : U => f x) := by
      funext x
      rfl
    rw [hfun]
    simpa only [coe_nnnorm, Real.norm_eq_abs] using he
  rw [hh, mul_add]

                                          
                                                              
                                                            
                                                                        
                      
                             
                                                   

                                          
                                                  
                                                                                      
                                                                

                                                                       
                                                                                 
                                                                  
                                                   
                                                             
                                                                                      
                                                     
                                                                           

end RothschildStein.H2

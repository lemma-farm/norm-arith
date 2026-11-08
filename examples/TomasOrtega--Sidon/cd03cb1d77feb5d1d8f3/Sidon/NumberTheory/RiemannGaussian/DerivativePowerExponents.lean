module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section

namespace RiemannGaussian.DerivativePowerExponents
noncomputable section

def alpha (k : ℕ) : ℝ := 1 / ((2 : ℝ) ^ (k + 2) - 2)

def amp (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ k

def beta (k : ℕ) : ℝ := 1 - amp k

theorem denominator_ge_two (k : ℕ) : 2 ≤ (2 : ℝ) ^ (k + 2) - 2 := by
  have h : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  linarith

theorem alpha_pos (k : ℕ) : 0 < alpha k := by
  unfold alpha
  have h := denominator_ge_two k
  positivity

                                                     
                                
              
                                                                   
          

                                                           

                                                                              
                                
              
                                                      
                                                        
                                                    
            
         
            

                                                                                           
                 
                       
            
      

                                         
            
            

                                            
            
                                                                                      

                                                 

                                                        
            
               
      

                                                                         

                                                         

                                                                 
             
               
      

end
end RiemannGaussian.DerivativePowerExponents

module

public import MeyerGeneralProblem.Cardinal.Strong.RationalTrigPerturbation
public import MeyerGeneralProblem.Cardinal.Strong.RationalComplexArithmetic
public import MeyerGeneralProblem.Cardinal.Strong.FiniteOriginalCoefficientBounds
public import Mathlib

@[expose] public section

/-! Ordinary unit-phase names with a size bound computed from the input name
itself. No supplied real-size or phase-accuracy certificate is used by the program. -/

namespace MeyerGeneralProblem.StrongParity

/-- Integer size budget read from the zero-precision rational input. -/
def rationalRealNameSize (name : ℕ → ℚ) : ℕ := ⌈|name 0|⌉₊ + 1

                                                                       
                                                      
                                               

                                                                              
                                                              
                                              
                                                                      

                                                                                        
                                                            
                                                                       

noncomputable section

/-- A valid binary real name supplies its actual size bound internally. -/
theorem rationalRealNameSize_bound (name : ℕ → ℚ) {x : ℝ}
    (hname : ∀ p, |(name p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ p) :
    |x| ≤ (rationalRealNameSize name : ℝ) := by
  have h0 := hname 0
  have hq : (|name 0| : ℚ) ≤ (⌈|name 0|⌉₊ : ℚ) := Nat.le_ceil _
  have hc : |(name 0 : ℝ)| ≤ (⌈|name 0|⌉₊ : ℝ) := by exact_mod_cast hq
  have h := abs_add_le (x - (name 0 : ℝ)) (name 0 : ℝ)
  rw [sub_add_cancel, abs_sub_comm] at h
  simp only [pow_zero, div_one] at h0
  simp only [rationalRealNameSize, Nat.cast_add, Nat.cast_one]
  linarith

/-- Every pi approximant has the fixed safe bound used by the phase program. -/
theorem rationalPiApprox_abs_le_five (p : ℕ) : |(rationalPiApprox p : ℝ)| ≤ 5 := by
  have he := rationalPiApprox_error p
  have hb : 1 / (2 : ℝ) ^ p ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ p)
  have h := abs_add_le ((rationalPiApprox p : ℝ) - Real.pi) Real.pi
  rw [sub_add_cancel, abs_of_pos Real.pi_pos] at h
  linarith [Real.pi_lt_four]

/-- The actual angle error includes BOTH the computed input and pi approximations. -/
theorem rationalNamedUnitPhase_angle_error (name : ℕ → ℚ) {x : ℝ}
    (hname : ∀ p, |(name p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ p) (p : ℕ) :
    |((2 * rationalPiApprox p * name p : ℚ) : ℝ) - 2 * Real.pi * x| ≤
      ((2 * (5 + rationalRealNameSize name) : ℕ) : ℝ) * (1 / (2 : ℝ) ^ p) := by
  have heq : ((2 * rationalPiApprox p * name p : ℚ) : ℝ) - 2 * Real.pi * x =
      2 * ((rationalPiApprox p : ℝ) * ((name p : ℝ) - x) +
        ((rationalPiApprox p : ℝ) - Real.pi) * x) := by push_cast; ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsum : |(rationalPiApprox p : ℝ) * ((name p : ℝ) - x) +
      ((rationalPiApprox p : ℝ) - Real.pi) * x| ≤
      5 * (1 / (2 : ℝ) ^ p) + (1 / (2 : ℝ) ^ p) * (rationalRealNameSize name : ℝ) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul (rationalPiApprox_abs_le_five p) (hname p) (abs_nonneg _) (by norm_num))
      (mul_le_mul (rationalPiApprox_error p) (rationalRealNameSize_bound name hname)
        (abs_nonneg _) (by positivity))
  calc
    _ ≤ 2 * (5 * (1 / (2 : ℝ) ^ p) +
      (1 / (2 : ℝ) ^ p) * (rationalRealNameSize name : ℝ)) := by linarith
    _ = _ := by push_cast; ring

                                                                             
                                                                     
                                                                      
                                              
                                                                 
                                                                 
                                                               
                                  
                                                               
                                  
                                                   
                                         
                                                                    

                                                                                    
                                                             
                                                                 
                                                                            
                                                                       
                                              
                                                            
                                                                 
                                                                 
                                                            
                                                                                
                                                   
         
                                                                                            
                                                                                     
                                                                                           
                      
                                       
                                                                     

                                                                                    
                                                           
                                                                 
                                                                                             
                                                                                           
                                                                            

                                                                                       
                                                                   
                                                                 
                                             

end

end MeyerGeneralProblem.StrongParity

module

public import MeyerGeneralProblem.Cardinal.Strong.RationalArctan
public import Mathlib

@[expose] public section

/-! Executable rational pi intervals from the ACTUAL arctangent evaluator. -/

namespace MeyerGeneralProblem.StrongParity

/-- A finite rational approximation to pi at the requested binary precision. -/
def rationalPiApprox (p : ℕ) : ℚ := 4 * rationalArctanApprox 1 (p + 2)

                                                               
                                                                              

                                                                           
                                                             

noncomputable section

                                                              
                                                                                 
                                                                            
                                         
                          
           
          

                                                                   
theorem rationalPiApprox_error (p : ℕ) :
    |(rationalPiApprox p : ℝ) - Real.pi| ≤ 1 / (2 : ℝ) ^ p := by
  have h := rationalArctanApprox_error 1 (p + 2)
  rw [Rat.cast_one, Real.arctan_one] at h
  have hi : (rationalPiApprox p : ℝ) - Real.pi =
      4 * ((rationalArctanApprox 1 (p + 2) : ℝ) - Real.pi / 4) := by
    simp only [rationalPiApprox, Rat.cast_mul, Rat.cast_ofNat]
    ring
  rw [hi, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc
    _ ≤ 4 * (1 / (2 : ℝ) ^ (p + 2)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by rw [pow_add]; norm_num; field_simp

                                                       
                                     
                                                                                
                                                    
                                                                      
                                               

                                                                  
                                                                                 
                                                            

                                                                       
                                       
          
                             
               

                                                              
                                           
                                                                           
                                                                                     
                                                        
                                                             
                                                    
                                                                                       
              
                                               
                                                                                
      
                                                                   
                                                                                       
                                
                                                                
                          

end

end MeyerGeneralProblem.StrongParity

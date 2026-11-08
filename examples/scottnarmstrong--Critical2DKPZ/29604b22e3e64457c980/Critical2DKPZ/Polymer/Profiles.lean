/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Endpoints
import Mathlib.Tactic

/-! An arbitrary terminal weight and a finitely supported initial profile define finite sums of polymer path weights. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Polymer

/-- The probabilities of all finite walk paths sum to one. -/
theorem sum_walkProbability (n : ℕ) :
    (∑ _s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_pow]

/-- With zero disorder strength, every path weight equals one. -/
@[simp]
theorem pathWeight_zero_beta (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) :
    pathWeight 0 a w s ω = 1 := by
  simp only [pathWeight, zero_mul, zero_pow (by decide : 2 ≠ 0),
    zero_div, sub_self, Finset.sum_const_zero, Real.exp_zero]

/-- With zero disorder strength, the point-to-point partition function equals the walk kernel. -/
theorem pointToPoint_zero_beta (a n : ℕ) (w z : Site) (ω : Disorder) :
    pointToPoint 0 a n w z ω = srwKernel n (z - w) := by
  rw [pointToPoint_eq_sum, srwKernel_eq_sum n w z]
  simp only [pathWeight_zero_beta, mul_one]

/-- With zero disorder strength, the point-to-plane partition function equals one. -/
theorem pointToPlane_zero_beta (a n : ℕ) (w : Site) (ω : Disorder) :
    pointToPlane 0 a n w ω = 1 := by
  rw [pointToPlane_eq_sum]
  simp only [pathWeight_zero_beta, mul_one, sum_walkProbability]

/-- The simple-walk transition kernel has total mass one. -/
theorem tsum_srwKernel (n : ℕ) (w : Site) :
    ∑' z, srwKernel n (z - w) = 1 := by
  have h := tsum_pointToPoint 0 0 n w (fun _ => 0)
  simpa only [pointToPoint_zero_beta, pointToPlane_zero_beta] using h

                                                                  
                                                    
                                                      
                           
      
                                                                     

                                             
                                                                  
                  
                                                               
                                 

                                                                           
                                                                         
                                       
                                                               
                                                                               
                                
                     
                           
                             
                                                                      
                         
                                                      
                                                  

                                                                          
                                                               
                                                         
                                      
                                                         
                                          
            
                                          
                                          
                                                        
                                                                
                                   

                                                           
                                                                    
                                             
                     
                                                     
                                                                                    

                                                                
                                                                         
                             
                                                                             
                                 
                                    
                                                             

                                                                                                
                                                                              
                                                              
                                           
                                 
                                     
                                                              
                                                                                  
                                                        
                                                                                 

                                                                                                                  
                                                              
                                                              
                              
                                                                     
                     
                                                         

                                                               
                                                                    
                                                                       
                                                      
                                              
                                                                     
            
                                              
          
                                    
                                                            

                                                                                    
                                                                       
                                               
                                                
                                                                
                                              
                                                                     
            
                                              
                                          
                                
                                                                       
                                                        

end Critical2DKPZ.Polymer

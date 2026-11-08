/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.SRW
public import Critical2DKPZ.RandomWalk.Port.Walk.OneDim

/-! # One-dimensional simple and lazy walk kernels

Two simple walk steps give a lazy step after dividing space by two; consequently
the simple walk kernel is bounded by `√2 / √(n+1)` at every site. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

/-- The `ℓ¹` norm of a one-dimensional site is the absolute value. -/
theorem graphNorm_one (a : ℤ) : graphNorm (![a] : Site 1) = a.natAbs := by
  simp [graphNorm]

/-- The simple walk at an even time and an even site is the lazy walk. -/
theorem srwHeat_one_two_mul (m : ℕ) (k : ℤ) :
    srwHeat 1 (2 * m) ![2 * k] = P1 m k := by
  induction m generalizing k with
  | zero =>
      rw [P1_zero_step]
      simp only [Nat.mul_zero]
      by_cases hk : k = 0
      · subst hk
        norm_num
        funext i
        exact i.elim0
      · rw [ite_eq_right hk, srwHeat_zero, ite_eq_right]
        intro hc
        apply hk
        have : (![2 * k] : Site 1) 0 = (0 : Site 1) 0 := by rw [hc]
        simp at this
        omega
  | succ m ih =>
      have hstep : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      rw [hstep, srwHeat_one_succ, srwHeat_one_succ, srwHeat_one_succ]
      have e1 : 2 * k - 1 - 1 = 2 * (k - 1) := by ring
      have e2 : 2 * k - 1 + 1 = 2 * k := by ring
      have e3 : 2 * k + 1 - 1 = 2 * k := by ring
      have e4 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      rw [e1, e2, e3, e4, ih, ih, ih]
      rw [P1_succ]
      ring

                                                                            
                                             
                                                              
                                                 
                                   
            
                                                                       
                                 
                                                              
                                                 
                                         
                        
                                                     
                                 
                 
               
                                              
            
                                                     
                 
                                              
            
                      
            
              
              

                                                          
                                        
                                                                  
                                                 
                                   
            
                                                
                                                        
                                                                                             
                                        
                                 
               
             
              
            
                                       
            
                         
                                             
                                             
                                                                   
                                           
                                                                                     
                                          
                                                         
          
             
            


                                                          

                                                                                
                                                                                 
                                           
                                                      
                                                                         
         
                  
           
                   
                                 
                                 
                        
                                                                          
                                         
                                            
              
                
                   
                         
                                       
                
                                                                                       
                           
                                                             
                                                                                     
                                                                                           
                                                        
                                                                   
                 
            
                           
                                     
                  
                                                                                      
                             
                                                                                      
                                                       
                                                                                          
                                                          
                                                         
                   
              
                               
                                                            
                                                                       
                                                          
                                                                       
                                                                                          
                   
                       
              

end LatticeProb

end

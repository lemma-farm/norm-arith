/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Exact partial-selfing recurrence -/

@[expose] public section

namespace Rhone.Dynamics.Inbreeding

                                                                     

                                                                

                                                        
                                                                              
                                               
            
      

                                                        
                      
                                                             
                                                    
                  
                
                
                                         
                                         
                                       
                 
                    

                                         
                                                             
                                                                 
                           
             
              
                                         
                                            
                     

                                       
                                          
                                                                 
                                                       
                                    
                                       
                                     
                                                            
                                                                      
                           
                                                                             

                                  
                                          
                                                                
                                                            
                                         
      

                                  
                                  
                                                                 
                                     
                                                                                     
                                                                                        

                                       
noncomputable def fullSibStep (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, (1 + 2 * z.2 + z.1) / 4)

                                                          
                        

                                                                             
             
           
                                  
                                  
                          
                                              
                                                
              
                        

                                    
                                                                     
                                                   
                                                         
                                                          
                               
                                            

                                       
theorem full_sib_deficit_recursion (z : ℝ × ℝ) :
    1 - (fullSibStep z).2 = (1 - z.2) / 2 + (1 - z.1) / 4 := by
  unfold fullSibStep
  ring

                                       
                                                                                
                        

                                       
                                                                                  
                                                      

private noncomputable def sibError (z : ℝ × ℝ) : ℝ := |1 - z.1| + 2 * |1 - z.2|

private theorem sibError_step (z : ℝ × ℝ) : sibError (fullSibStep z) ≤ sibError z := by
  have h := abs_add_le ((1 - z.2) / 2) ((1 - z.1) / 4)
  rw [abs_div, abs_div] at h
  norm_num at h
  have he := full_sib_deficit_recursion z
  unfold sibError
  change |1 - z.2| + 2 * |1 - (fullSibStep z).2| ≤ _
  rw [he]
  linarith [abs_nonneg (1 - z.1)]

private theorem sibError_two_steps (z : ℝ × ℝ) :
    sibError (fullSibStep (fullSibStep z)) ≤ (3 / 4 : ℝ) * sibError z := by
  have hfirst : 1 - (fullSibStep (fullSibStep z)).1 =
      (1 - z.1) / 4 + (1 - z.2) / 2 := by simp [fullSibStep]; ring
  have hsecond : 1 - (fullSibStep (fullSibStep z)).2 =
      (1 - z.1) / 8 + (1 - z.2) / 2 := by simp [fullSibStep]; ring
  have h1 := abs_add_le ((1 - z.1) / 4) ((1 - z.2) / 2)
  have h2 := abs_add_le ((1 - z.1) / 8) ((1 - z.2) / 2)
  rw [abs_div, abs_div] at h1 h2
  norm_num at h1 h2
  unfold sibError
  rw [hfirst, hsecond]
  linarith [abs_nonneg (1 - z.1)]

private theorem sibError_iterate (z : ℝ × ℝ) (t : ℕ) :
    sibError ((fullSibStep^[t]) z) ≤ (3 / 4 : ℝ) ^ (t / 2) * sibError z := by
  induction t using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using sibError_step z
  | more t ih _ =>
    have ht : (t + 2) / 2 = t / 2 + 1 := by omega
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ht, pow_succ]
    calc
      sibError (fullSibStep (fullSibStep ((fullSibStep^[t]) z))) ≤
          (3 / 4 : ℝ) * sibError ((fullSibStep^[t]) z) := sibError_two_steps _
      _ ≤ (3 / 4 : ℝ) * ((3 / 4 : ℝ) ^ (t / 2) * sibError z) := by
        exact mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by ring

                                       
                                      
                                                     
                                                
                                                                                 
                                             
                                                                 
         
                                                        
                                                                                         
                  
                                
                                                                          
                                    
                                                                       
                                                                    
                                                                 
                                       
                                             
                                
                                                                           
                                          
                       
                                                     
                                                            
                                                                 
                                       
                                             
                                
                                                                           
                                          
                       
                                                     
                                                           
                                                           
                 
                         

end Rhone.Dynamics.Inbreeding

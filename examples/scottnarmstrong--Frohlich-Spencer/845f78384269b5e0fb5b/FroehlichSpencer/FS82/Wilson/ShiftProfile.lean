/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The transverse profile of the explicit loop shift

* `uni d` is the uniform weight `1/(d+1)` on `{0,…,d}` and `ramp d` is
  `j/((d+1)(d+2))` on `{1,…,d+1}`; `ramp d (j+1) - ramp d j = uni d j - uni (d+1) j`.
* `levelTwo d`, `levelThree d` are the two components of the level field `b_d` in the
  transverse `2–3` plane, with `curl b_d = u_d ⊗ u_d - u_{d+1} ⊗ u_{d+1}`.
* `shiftTwo d`, `shiftThree d` are the components of `a_d = Σ_{j<d} b_j`, with
  `curl a_d = u_0 ⊗ u_0 - u_d ⊗ u_d`: the unit flux of one plaquette is spread
  uniformly over the square `{0,…,d}²`.
* The squared norms are bounded over every finite index set, and the tent sums used for
  the perimeter bookkeeping are bounded.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open Finset

                                                        
                                                      
                                                      

                                                       
                                                       
                                                                                  


                                                                 
            
                    
           
        
                                                

                                                                                 
              
                                               

                                                                                       
              
                                                

                                       
                                                                                           
                                       
                                                             
                                                  
                                                  
                 
                                                                 
         
                        
                                                 
                                       
                                                 
                                                 
                                                 

                                                                                    
                                                                                         
                                        

                                                 
                                                                    
             
                                             
        
                                                         
                                                    
                                                       

                                                

                                                                                             
                                                      
theorem sum_le_sum_range_of_param (f : ℤ → ℝ) (hf : ∀ j, 0 ≤ f j) (n : ℕ) (e : ℕ → ℤ)
    (hsupp : ∀ j, f j ≠ 0 → ∃ k, k < n ∧ e k = j) (s : Finset ℤ) :
    ∑ j ∈ s, f j ≤ ∑ k ∈ range n, f (e k) := by
  classical
  calc ∑ j ∈ s, f j = ∑ j ∈ s with f j ≠ 0, f j := (sum_filter_ne_zero s).symm
    _ ≤ ∑ j ∈ (range n).image e, f j := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨k, hk, rfl⟩ := hsupp j (mem_filter.mp hj).2
          exact mem_image.mpr ⟨k, mem_range.mpr hk, rfl⟩
        · intro j _ _
          exact hf j
    _ ≤ ∑ k ∈ range n, f (e k) := sum_image_le_of_nonneg fun _ _ => hf _

                                      
                                                                                
                  
                
                
                           
             
        

                                                      
                                              
                                                  
                                                  
                                                                                     
                              
       
                
                                                   
                
                                
                                             
                                
                                   
                                                                 
                                          
           
            

                                                            
                                                     
                                                         

                                                          
                   
            

                                                                   
                                               
                                              
                                                  
                                                  
                                                                                      
                              
       
                
                                                    
                
                                
                                             
                                
                                   
                                                                           
                                                          
           
            
      

                                                                

                                                       
                                                                                         

                                                       
                                                                                  

                                                     
                                                                                           

                                                     
                                                                                               

                                                                                  

                                                                                        

                                         
                                                                
                                 

                                           
                                                                      
                                   

                                                  
                                      
                                                                                           
                                                             
                              
                              
                            
                                                          

                                          
                                      
                                                                                           
                                                 
                  
                
                
                               
                                              
                              

                                                                     
                                                               
                      
                                                               
                                                          
                           
                            
                         
              
                   
            

                                                                         
                                                           
                        
                                                          
                                                         
                                         

                                                             
                                                                     
                                                       
                      
                                                        
                                     
                                 
       

                                                                         
                                                       
                        
                                                        
                                     
                                   
       

                                                

                                                                       
                                                   
                                                                           
                                                  
                              
                              
                                                                          
                                                                          
                                                
                                                           
                        
                                                                             
                                                                                         
                                   
                  

                                                                                             
@[expose] noncomputable def levelBound (d : ℕ) : ℝ :=
  (1 / 3) * (1 / ((d : ℝ) + 1) ^ 2 + 1 / ((d : ℝ) + 2) ^ 2)

theorem levelBound_nonneg (d : ℕ) : 0 ≤ levelBound d := by
  unfold levelBound
  positivity

                                   
                                                                               
                                                  
                                                  
                                                                     
                                                                 
                     
              
        
                      
                                                          
                                                               
                                                               
                                                                                         
                                                                                         
             
          

                                                                     
                                                  
                                                                                      
                                                  
                                                  
                                     
                               
                                
                                
                                                                  
                                  
             
        
                                                                               
                                                                          
                                                                          
                                                                         
                                
                                                  
                                                                
                    
                                                               
                   
        
                                                    
                                                          
                    
                                                               
                     
        
                                                                  
                                                                                  
                                                            
                                                                    
                                                                    
                                                                                           
                                   
                                                                                     
                   
                              
                                                                         
                                           

                               

                                          
theorem sum_inv_sq_le (m : ℕ) :
    ∑ r ∈ range (m + 1), 1 / ((r : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((m : ℝ) + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ]
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have step : 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
        1 / ((m : ℝ) + 1) - 1 / (((m + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ h1.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `Σ_{r ≤ m} 1/(r+2)² ≤ 1 - 1/(m+2)`. -/
theorem sum_inv_sq_shift_le (m : ℕ) :
    ∑ r ∈ range (m + 1), 1 / ((r : ℝ) + 2) ^ 2 ≤ 1 - 1 / ((m : ℝ) + 2) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ]
    have h2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h3 : (0 : ℝ) < (m : ℝ) + 3 := by positivity
    have step : 1 / (((m + 1 : ℕ) : ℝ) + 2) ^ 2 ≤
        1 / ((m : ℝ) + 2) - 1 / (((m + 1 : ℕ) : ℝ) + 2) := by
      push_cast
      rw [div_sub_div _ _ h2.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem inv_sq_min_le (a b : ℕ) (c : ℝ) (hc : 0 < c) :
    1 / (((min a b : ℕ) : ℝ) + c) ^ 2 ≤ 1 / ((a : ℝ) + c) ^ 2 + 1 / ((b : ℝ) + c) ^ 2 := by
  have ha : (0 : ℝ) ≤ 1 / ((a : ℝ) + c) ^ 2 := by positivity
  have hb : (0 : ℝ) ≤ 1 / ((b : ℝ) + c) ^ 2 := by positivity
  rcases le_total a b with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

theorem sum_range_reflect_inv_sq (m : ℕ) (c : ℝ) :
    ∑ y ∈ range (m + 1), 1 / (((m - y : ℕ) : ℝ) + c) ^ 2 =
      ∑ y ∈ range (m + 1), 1 / ((y : ℝ) + c) ^ 2 := by
  have h := sum_range_reflect (fun y : ℕ => 1 / ((y : ℝ) + c) ^ 2) (m + 1)
  simpa using h

/-- A row of the sheet: `Σ_{y ≤ m} 1/(min(y, m-y)+1)² ≤ 4`. -/
theorem tent_sum_le (m : ℕ) :
    ∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 1) ^ 2 ≤ 4 := by
  have hS := sum_inv_sq_le m
  have hm : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
  calc ∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 1) ^ 2
      ≤ ∑ y ∈ range (m + 1),
          (1 / ((y : ℝ) + 1) ^ 2 + 1 / (((m - y : ℕ) : ℝ) + 1) ^ 2) :=
        sum_le_sum fun y _ => inv_sq_min_le y (m - y) 1 one_pos
    _ = ∑ y ∈ range (m + 1), 1 / ((y : ℝ) + 1) ^ 2 +
          ∑ y ∈ range (m + 1), 1 / ((y : ℝ) + 1) ^ 2 := by
        rw [sum_add_distrib, sum_range_reflect_inv_sq]
    _ ≤ 4 := by linarith

/-- `Σ_{y ≤ m} 1/(min(y, m-y)+2)² ≤ 2`. -/
theorem tent_sum_shift_le (m : ℕ) :
    ∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 2) ^ 2 ≤ 2 := by
  have hS := sum_inv_sq_shift_le m
  have hm : (0 : ℝ) ≤ 1 / ((m : ℝ) + 2) := by positivity
  calc ∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 2) ^ 2
      ≤ ∑ y ∈ range (m + 1),
          (1 / ((y : ℝ) + 2) ^ 2 + 1 / (((m - y : ℕ) : ℝ) + 2) ^ 2) :=
        sum_le_sum fun y _ => inv_sq_min_le y (m - y) 2 two_pos
    _ = ∑ y ∈ range (m + 1), 1 / ((y : ℝ) + 2) ^ 2 +
          ∑ y ∈ range (m + 1), 1 / ((y : ℝ) + 2) ^ 2 := by
        rw [sum_add_distrib, sum_range_reflect_inv_sq]
    _ ≤ 2 := by linarith

/-- One row of walls: `Σ_{y ≤ m} levelBound (min(y, m-y)) ≤ 2`. -/
theorem tent_levelBound_sum_le (m : ℕ) :
    ∑ y ∈ range (m + 1), levelBound (min y (m - y)) ≤ 2 := by
  have h1 := tent_sum_le m
  have h2 := tent_sum_shift_le m
  have e : ∑ y ∈ range (m + 1), levelBound (min y (m - y)) =
      (1 / 3) * (∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 1) ^ 2 +
        ∑ y ∈ range (m + 1), 1 / (((min y (m - y) : ℕ) : ℝ) + 2) ^ 2) := by
    rw [← sum_add_distrib, mul_sum]
    rfl
  rw [e]
  linarith

                                                                  
                                                                              
                                
                                               
                                                                           
                                               
                                                  
                                                                         
                                                   
                                                      
                                                         
                                                                                 
                                                                                         
                                                                                               
                                                                                 
                 
            
                                                   
              
                             
                             
                                                      

end FroehlichSpencer.FS82.Wilson

end

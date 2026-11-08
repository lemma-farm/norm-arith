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

/-- `u_d`: the uniform weight `1/(d+1)` on `{0,…,d}`. -/
@[expose] noncomputable def uni (d : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ (d : ℤ) then 1 / ((d : ℝ) + 1) else 0

/-- `X_d`: the ramp `j/((d+1)(d+2))` on `{1,…,d+1}`. -/
@[expose] noncomputable def ramp (d : ℕ) (j : ℤ) : ℝ :=
  if 1 ≤ j ∧ j ≤ (d : ℤ) + 1 then (j : ℝ) / (((d : ℝ) + 1) * ((d : ℝ) + 2)) else 0


                                                                 
            
                    
           
        
                                                

theorem uni_ne_zero {d : ℕ} {j : ℤ} (h : uni d j ≠ 0) : 0 ≤ j ∧ j ≤ (d : ℤ) := by
  by_contra hc
  exact h (by unfold uni; rw [ite_eq_right hc])

theorem ramp_ne_zero {d : ℕ} {j : ℤ} (h : ramp d j ≠ 0) : 1 ≤ j ∧ j ≤ (d : ℤ) + 1 := by
  by_contra hc
  exact h (by unfold ramp; rw [ite_eq_right hc])

                                       
                                                                                           
                                       
                                                             
                                                  
                                                  
                 
                                                                 
         
                        
                                                 
                                       
                                                 
                                                 
                                                 

theorem uni_natCast (d j : ℕ) (hj : j ≤ d) : uni d (j : ℤ) = 1 / ((d : ℝ) + 1) := by
  have h : (0 : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) ≤ (d : ℤ) := ⟨by positivity, by exact_mod_cast hj⟩
  simp only [uni, h, and_self, ite_true]

theorem ramp_natCast (d j : ℕ) (hj : j ≤ d + 1) :
    ramp d (j : ℤ) = (j : ℝ) / (((d : ℝ) + 1) * ((d : ℝ) + 2)) := by
  unfold ramp
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · simp
  · have h : (1 : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) ≤ (d : ℤ) + 1 :=
      ⟨by exact_mod_cast hpos, by exact_mod_cast hj⟩
    simp only [h, and_self, ite_true, Int.cast_natCast]

/-! ### Sums over arbitrary finite index sets -/

/-- A nonnegative function on `ℤ` whose support is parametrized by `e` on `range n` has every
finite partial sum bounded by the parametrized sum. -/
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

theorem sum_range_natCast_sq (n : ℕ) :
    ∑ j ∈ range (n + 1), (j : ℝ) ^ 2 = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- `‖u_d‖² ≤ 1/(d+1)` over every finite index set. -/
theorem sum_uni_sq_le (d : ℕ) (s : Finset ℤ) :
    ∑ j ∈ s, uni d j ^ 2 ≤ 1 / ((d : ℝ) + 1) := by
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hle := sum_le_sum_range_of_param (fun j => uni d j ^ 2) (fun j => sq_nonneg _)
    (d + 1) (fun k => (k : ℤ))
    (by
      intro j hj
      have hj' := uni_ne_zero (d := d) (j := j) (by
        intro h0
        exact hj (by simp [h0]))
      refine ⟨j.toNat, by omega, by omega⟩) s
  refine hle.trans (le_of_eq ?_)
  rw [sum_congr rfl (fun j hj => by
    rw [uni_natCast d j (Nat.lt_succ_iff.mp (mem_range.mp hj))])]
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  field_simp

/-- The squared norm of the ramp, `(2d+3)/(6(d+1)(d+2))`. -/
@[expose] noncomputable def rampNormSq (d : ℕ) : ℝ :=
  (2 * (d : ℝ) + 3) / (6 * ((d : ℝ) + 1) * ((d : ℝ) + 2))

theorem rampNormSq_nonneg (d : ℕ) : 0 ≤ rampNormSq d := by
  unfold rampNormSq
  positivity

/-- `‖X_d‖² ≤ (2d+3)/(6(d+1)(d+2))` over every finite index set. -/
theorem sum_ramp_sq_le (d : ℕ) (s : Finset ℤ) :
    ∑ j ∈ s, ramp d j ^ 2 ≤ rampNormSq d := by
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hle := sum_le_sum_range_of_param (fun j => ramp d j ^ 2) (fun j => sq_nonneg _)
    (d + 2) (fun k => (k : ℤ))
    (by
      intro j hj
      have hj' := ramp_ne_zero (d := d) (j := j) (by
        intro h0
        exact hj (by simp [h0]))
      refine ⟨j.toNat, by omega, by omega⟩) s
  refine hle.trans (le_of_eq ?_)
  rw [sum_congr rfl (fun j hj => by
    rw [ramp_natCast d j (Nat.lt_succ_iff.mp (mem_range.mp hj)), div_pow])]
  rw [← sum_div, sum_range_natCast_sq (d + 1), rampNormSq]
  push_cast
  field_simp
  ring

/-! ### The level field and the shift in the transverse plane -/

/-- Component along axis 2 of the level field `b_d`. -/
@[expose] noncomputable def levelTwo (d : ℕ) (y z : ℤ) : ℝ := -(uni (d + 1) y * ramp d z)

/-- Component along axis 3 of the level field `b_d`. -/
@[expose] noncomputable def levelThree (d : ℕ) (y z : ℤ) : ℝ := ramp d y * uni d z

/-- Component along axis 2 of `a_d = Σ_{j<d} b_j`. -/
@[expose] noncomputable def shiftTwo (d : ℕ) (y z : ℤ) : ℝ := ∑ j ∈ range d, levelTwo j y z

/-- Component along axis 3 of `a_d = Σ_{j<d} b_j`. -/
@[expose] noncomputable def shiftThree (d : ℕ) (y z : ℤ) : ℝ := ∑ j ∈ range d, levelThree j y z

                                                                                  

                                                                                        

theorem shiftTwo_succ (d : ℕ) (y z : ℤ) :
    shiftTwo (d + 1) y z = shiftTwo d y z + levelTwo d y z := by
  simp [shiftTwo, sum_range_succ]

theorem shiftThree_succ (d : ℕ) (y z : ℤ) :
    shiftThree (d + 1) y z = shiftThree d y z + levelThree d y z := by
  simp [shiftThree, sum_range_succ]

                                                  
                                      
                                                                                           
                                                             
                              
                              
                            
                                                          

                                          
                                      
                                                                                           
                                                 
                  
                
                
                               
                                              
                              

                                                                     
                                                               
                      
                                                               
                                                          
                           
                            
                         
              
                   
            

                                                                         
                                                           
                        
                                                          
                                                         
                                         

                                                             
                                                                     
                                                       
                      
                                                        
                                     
                                 
       

                                                                         
                                                       
                        
                                                        
                                     
                                   
       

                                                

                                                                       
                                                   
                                                                           
                                                  
                              
                              
                                                                          
                                                                          
                                                
                                                           
                        
                                                                             
                                                                                         
                                   
                  

                                                                                             
@[expose] noncomputable def levelBound (d : ℕ) : ℝ :=
  (1 / 3) * (1 / ((d : ℝ) + 1) ^ 2 + 1 / ((d : ℝ) + 2) ^ 2)

                                                          
                   
            

theorem rampNormSq_mul_le (d : ℕ) :
    rampNormSq d * (1 / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 2)) ≤ levelBound d := by
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have key : rampNormSq d * (1 / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 2)) =
      (1 / 6) * (1 / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 2)) ^ 2 := by
    unfold rampNormSq
    field_simp
    ring
  rw [key, levelBound]
  have hsq : (1 / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 2)) ^ 2 ≤
      2 * (1 / ((d : ℝ) + 1) ^ 2 + 1 / ((d : ℝ) + 2) ^ 2) := by
    have h := sq_nonneg (1 / ((d : ℝ) + 1) - 1 / ((d : ℝ) + 2))
    have e1 : (1 / ((d : ℝ) + 1)) ^ 2 = 1 / ((d : ℝ) + 1) ^ 2 := by rw [div_pow, one_pow]
    have e2 : (1 / ((d : ℝ) + 2)) ^ 2 = 1 / ((d : ℝ) + 2) ^ 2 := by rw [div_pow, one_pow]
    nlinarith
  linarith

/-- The level field `b_d` has squared norm at most `levelBound d`. -/
theorem sum_level_sq_le (d : ℕ) (s t : Finset ℤ) :
    ∑ y ∈ s, ∑ z ∈ t, (levelTwo d y z ^ 2 + levelThree d y z ^ 2) ≤ levelBound d := by
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hu1 := sum_uni_sq_le (d + 1) s
  have hu0 := sum_uni_sq_le d t
  have hrs := sum_ramp_sq_le d s
  have hrt := sum_ramp_sq_le d t
  have hu1' : ∑ y ∈ s, uni (d + 1) y ^ 2 ≤ 1 / ((d : ℝ) + 2) := by
    refine hu1.trans (le_of_eq ?_)
    push_cast
    ring
  have n1 : 0 ≤ ∑ y ∈ s, uni (d + 1) y ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have n2 : 0 ≤ ∑ z ∈ t, ramp d z ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have n3 : 0 ≤ ∑ y ∈ s, ramp d y ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have n4 : 0 ≤ ∑ z ∈ t, uni d z ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hR := rampNormSq_nonneg d
  have e2 : ∑ y ∈ s, ∑ z ∈ t, levelTwo d y z ^ 2 =
      (∑ y ∈ s, uni (d + 1) y ^ 2) * ∑ z ∈ t, ramp d z ^ 2 := by
    rw [sum_mul_sum]
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    unfold levelTwo
    ring
  have e3 : ∑ y ∈ s, ∑ z ∈ t, levelThree d y z ^ 2 =
      (∑ y ∈ s, ramp d y ^ 2) * ∑ z ∈ t, uni d z ^ 2 := by
    rw [sum_mul_sum]
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    unfold levelThree
    ring
  have b2 : (∑ y ∈ s, uni (d + 1) y ^ 2) * ∑ z ∈ t, ramp d z ^ 2 ≤
      (1 / ((d : ℝ) + 2)) * rampNormSq d := mul_le_mul hu1' hrt n2 (by positivity)
  have b3 : (∑ y ∈ s, ramp d y ^ 2) * ∑ z ∈ t, uni d z ^ 2 ≤
      rampNormSq d * (1 / ((d : ℝ) + 1)) := mul_le_mul hrs hu0 n4 hR
  calc ∑ y ∈ s, ∑ z ∈ t, (levelTwo d y z ^ 2 + levelThree d y z ^ 2)
      = ∑ y ∈ s, ∑ z ∈ t, levelTwo d y z ^ 2 + ∑ y ∈ s, ∑ z ∈ t, levelThree d y z ^ 2 := by
        simp only [sum_add_distrib]
    _ ≤ (1 / ((d : ℝ) + 2)) * rampNormSq d + rampNormSq d * (1 / ((d : ℝ) + 1)) := by
        rw [e2, e3]
        exact add_le_add b2 b3
    _ = rampNormSq d * (1 / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 2)) := by ring
    _ ≤ levelBound d := rampNormSq_mul_le d

/-! ### Series and tent sums -/

                                          
                               
                                                                            
                  
                    
                
                       
                                                    
                                                    
                                                 
                                                             
               
                                                                                                  
               
            

                                          
                                     
                                                                            
                  
                    
                
                       
                                                    
                                                    
                                                 
                                                             
               
                                                                                                  
               
            

                                                      
                                                                                           
                                                            
                                                            
                                
                                
                                 

                                                  
                                                          
                                                      
                                                                          
               

                                                              
                             
                                                                          
                            
                                                        
                                                                   
                            
                                                                      
                                                               
                                                    
                                                          
                                                      
                        

                                          
                                   
                                                                          
                                  
                                                        
                                                                   
                            
                                                                      
                                                               
                                                    
                                                          
                                                      
                        

                                                                  
                                        
                                                             
                          
                                
                                                            
                                                                               
                                                                           
                                   
       
        
          

                                                                  
                                                                              
                                
                                               
                                                                           
                                               
                                                  
                                                                         
                                                   
                                                      
                                                         
                                                                                 
                                                                                         
                                                                                               
                                                                                 
                 
            
                                                   
              
                             
                             
                                                      

end FroehlichSpencer.FS82.Wilson

end

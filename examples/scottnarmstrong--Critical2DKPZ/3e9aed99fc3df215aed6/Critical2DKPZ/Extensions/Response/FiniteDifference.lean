/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow
/-!
# Finite differences of scalar functions

Generic estimates used in Lemma 4.2 of the four-results note.
-/

public section

namespace Critical2DKPZ.Extensions.Response

/-- The first forward difference has an error bounded by half the second-derivative bound. -/
theorem first_difference_error_le (f : ℝ → ℝ) (x ε B : ℝ)
    (hε : 0 < ε) (hf : ContDiff ℝ 2 f)
    (hf2 : ∀ y ∈ Set.Icc x (x + ε), |iteratedDeriv 2 f y| ≤ B) :
    |f (x + ε) - f x - ε * deriv f x| ≤ B * ε ^ 2 / 2 := by
  have hxx : x < x + ε := by linarith
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) (ne_of_lt hxx) hf.contDiffOn
  rw [Set.uIoo_of_lt hxx] at hy
  have hpoly : taylorWithinEval f 1 (Set.uIcc x (x + ε)) x (x + ε) =
      f x + ε * deriv f x := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (ne_of_lt hxx))
        (hf.of_le (by norm_num)).contDiffAt (by simp [hε.le])]
    simp [iteratedDeriv_one]
  rw [hpoly] at heq
  have hb := hf2 y ⟨hy.1.le, hy.2.le⟩
  have hr : f (x + ε) - f x - ε * deriv f x =
      iteratedDeriv 2 f y * ε ^ 2 / 2 := by
    simpa [Nat.factorial, sub_add_eq_sub_sub] using heq
  rw [hr, abs_div, abs_mul, abs_pow, abs_of_pos hε, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb (sq_nonneg ε)) (by norm_num)

/-- Comparison of first derivatives from uniform function and second derivative bounds
on the enlarged interval (Lemma 4.2(a)). -/
theorem deriv_sub_le_of_finiteDifference (f g : ℝ → ℝ) (a b ε B E : ℝ)
    (_hab : a ≤ b) (hε : 0 < ε) (_hB : 0 ≤ B) (_hE : 0 ≤ E)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfg : ∀ x ∈ Set.Icc a (b + ε), |f x - g x| ≤ E)
    (hf2 : ∀ x ∈ Set.Icc a (b + ε), |iteratedDeriv 2 f x| ≤ B)
    (hg2 : ∀ x ∈ Set.Icc a (b + ε), |iteratedDeriv 2 g x| ≤ B) :
    ∀ x ∈ Set.Icc a b, |deriv f x - deriv g x| ≤ 2 * E / ε + B * ε := by
  intro x hx
  have hsub : Set.Icc x (x + ε) ⊆ Set.Icc a (b + ε) := by
    intro y hy
    exact ⟨hx.1.trans hy.1, by linarith [hy.2, hx.2]⟩
  have hfx := first_difference_error_le f x ε B hε hf (fun y hy => hf2 y (hsub hy))
  have hgx := first_difference_error_le g x ε B hε hg (fun y hy => hg2 y (hsub hy))
  have h0 := hfg x ⟨hx.1, by linarith [hx.2]⟩
  have h1 := hfg (x + ε) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd : |ε * (deriv f x - deriv g x)| ≤ 2 * E + B * ε ^ 2 := by
    have hid : ε * (deriv f x - deriv g x) =
        (f (x + ε) - g (x + ε)) - (f x - g x) -
        (f (x + ε) - f x - ε * deriv f x) +
        (g (x + ε) - g x - ε * deriv g x) := by ring
    rw [hid]
    calc
      _ ≤ |f (x + ε) - g (x + ε)| + |f x - g x| +
          |f (x + ε) - f x - ε * deriv f x| +
          |g (x + ε) - g x - ε * deriv g x| := by
        have ha := abs_sub (f (x + ε) - g (x + ε)) (f x - g x)
        have hb := abs_sub (f (x + ε) - g (x + ε) - (f x - g x))
          (f (x + ε) - f x - ε * deriv f x)
        have hc := abs_add_le
          (f (x + ε) - g (x + ε) - (f x - g x) -
            (f (x + ε) - f x - ε * deriv f x))
          (g (x + ε) - g x - ε * deriv g x)
        linarith only [ha, hb, hc]
      _ ≤ 2 * E + B * ε ^ 2 := by linarith only [h0, h1, hfx, hgx]
  rw [abs_mul, abs_of_pos hε] at hd
  apply (mul_le_mul_iff_right₀ hε).1
  calc
    ε * |deriv f x - deriv g x| ≤ 2 * E + B * ε ^ 2 := by
      exact hd
    _ = ε * (2 * E / ε + B * ε) := by field_simp

/-- A cubic comparison bounds the second forward difference whenever the second jet
component is bounded above by an affine function. -/
theorem second_difference_le_of_second_deriv_le (f f₁ f₂ : ℝ → ℝ)
    (x ε c B : ℝ) (hε : 0 < ε)
    (hf : ∀ y, HasDerivAt f (f₁ y) y)
    (hf₁ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + 2 * ε), f₂ y ≤ c + B * (y - x)) :
    f (x + 2 * ε) - 2 * f (x + ε) + f x ≤ c * ε ^ 2 + B * ε ^ 3 := by
  let F : ℝ → ℝ := fun y => f y - c / 2 * (y - x) ^ 2 - B / 6 * (y - x) ^ 3
  let F₁ : ℝ → ℝ := fun y => f₁ y - c * (y - x) - B / 2 * (y - x) ^ 2
  let F₂ : ℝ → ℝ := fun y => f₂ y - c - B * (y - x)
  have hd : ∀ y, HasDerivAt F (F₁ y) y := by
    intro y
    convert ((hf y).sub (((hasDerivAt_id y).sub_const x).pow 2 |>.const_mul (c / 2))).sub
      (((hasDerivAt_id y).sub_const x).pow 3 |>.const_mul (B / 6)) using 1
    · rfl
    · dsimp [F₁]
      ring
  have hd₁ : ∀ y, HasDerivAt F₁ (F₂ y) y := by
    intro y
    convert ((hf₁ y).sub (((hasDerivAt_id y).sub_const x).const_mul c)).sub
      (((hasDerivAt_id y).sub_const x).pow 2 |>.const_mul (B / 2)) using 1
    · rfl
    · dsimp [F₂]
      ring
  have hc : ConcaveOn ℝ (Set.Icc x (x + 2 * ε)) F := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).hasDerivWithinAt) (fun y _ => (hd₁ y).hasDerivWithinAt)
    intro y hy
    have hb := hbound y (interior_subset hy)
    dsimp [F₂]
    linarith only [hb]
  have hh := hc.2 (show x ∈ Set.Icc x (x + 2 * ε) by constructor <;> linarith)
    (show x + 2 * ε ∈ Set.Icc x (x + 2 * ε) by constructor <;> linarith)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have heq : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (x + 2 * ε) = x + ε := by
    simp only [smul_eq_mul]; ring
  rw [heq] at hh
  dsimp [F] at hh
  nlinarith only [hh]

/-- Error of the second forward difference for a jet with Lipschitz second component. -/
theorem second_diff_quotient_error_le (f f₁ f₂ : ℝ → ℝ) (x ε B : ℝ)
    (hε : 0 < ε) (hf : ∀ y, HasDerivAt f (f₁ y) y)
    (hf₁ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (hLip : ∀ y ∈ Set.Icc x (x + 2 * ε), |f₂ y - f₂ x| ≤ B * |y - x|) :
    |(f (x + 2 * ε) - 2 * f (x + ε) + f x) / ε ^ 2 - f₂ x| ≤ B * ε := by
  have hu := second_difference_le_of_second_deriv_le f f₁ f₂ x ε (f₂ x) B hε hf hf₁
    (fun y hy => by
      have h := (abs_le.mp (hLip y hy)).2
      rw [abs_of_nonneg (sub_nonneg.mpr hy.1)] at h
      linarith only [h])
  have hl := second_difference_le_of_second_deriv_le (fun y => -f y)
    (fun y => -f₁ y) (fun y => -f₂ y) x ε (-f₂ x) B hε
    (fun y => (hf y).neg) (fun y => (hf₁ y).neg)
    (fun y hy => by
      have h := (abs_le.mp (hLip y hy)).1
      rw [abs_of_nonneg (sub_nonneg.mpr hy.1)] at h
      linarith only [h])
  have heq : (f (x + 2 * ε) - 2 * f (x + ε) + f x) / ε ^ 2 - f₂ x =
      (f (x + 2 * ε) - 2 * f (x + ε) + f x - f₂ x * ε ^ 2) / ε ^ 2 := by
    field_simp
  rw [heq, abs_le]
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    nlinarith only [hl]
  · apply (div_le_iff₀ (sq_pos_of_pos hε)).2
    nlinarith only [hu]

                                                                                      
                                           
                                                                                  
                                                           
                                               
                                                        
                                                                  
                                                                    
                                                                    
                                     
            
                                             
                                                                      
                                                                                         
                                                                                
                                                               
             
                                                                                  
                                                                      
                
                                                                        
                                                                                         
                                                          
                                                 
                                                            
                                                                                           
                                          
                                            
                           
                           
                                                         
                                                         
                                             
                                                                 
                                                                     
                                                      
                                                          
                                                      
                                               
                                                                                              
            
                                                            
                                              
                                                                                    
                                                              
                                      
                                           
                  
                                                          
                                                       
                                                                          
                                                                                         
                                                                                
                                                          
                
                                                                                         
                                      

                                                                             
                            
                                                                     
                                       
                                                  
                                                            
                                                            
                                                                       
                                                                     
                                       
                                                      
                                                                
                                                                
                                                                      
                                     
                                                                                  

end Critical2DKPZ.Extensions.Response

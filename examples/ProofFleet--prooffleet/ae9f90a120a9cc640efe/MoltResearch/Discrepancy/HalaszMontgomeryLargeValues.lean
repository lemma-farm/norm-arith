import MoltResearch.Discrepancy.LargeValues
import MoltResearch.Discrepancy.LogDifferences
import MoltResearch.Discrepancy.VinogradovTypeI

/-!
# Halász–Montgomery large values

This leaf develops the elementary Hilbert-space and exponential-sum argument
behind Iwaniec–Kowalski, Theorem 9.6.  The first unit is the finite-dimensional
duality step: the squared norm of a synthesis operator is controlled by the
largest absolute row sum of its Gram kernel.
-/

namespace MoltResearch

open Finset

                                                                  
                                                             
                                              
                                                              
                                       
                                               
           
                                       
                                               
             
                                                  
                                     
                                               
                                              
                                                                   
                                                 
                                                       
                                 
                                             
                                 
                                             
        
                                                      
                                                     
                        
                                             
                                             
                   
                    
                                                           
                                               
                                               
                                  
                                             
                                       
                                             
        
                         

                                                                    
                                                                              
                                                                       
                                                                               
                                                            
                                                               
                                                             
                                                          
                         
                  
                                                                
                      
                                      
           
                                                                  
                                 
                                 
                                                              
                                      
                                            
                                                              
                                                           
                 
                                                                    
                           
                                                    
                                               
                          
                        
                 
                           
                                              
        
                             
                                             
                                            
                                           
                                                              
                      
                                                              
                           
                                                     
                                                     
                                               
                                                                            
              
                                                                   
                                          
                                                                
                                                                                  
                                           
                                                                  
                                                                        
                           
                                                
                                                          
             
                                                                               
                                                             
                                   
        
                                       
                                    
                                                              
        
                                    
                                          
                                                                       
                                                                 
                                             
                                    
                                          
                                                                       
                            
                                                 
                            
                                    
                                        
                                                         
                                                                              
                                            
                                       
            
                           
                                        
                                                                  
                                                                                 
                                           
                                       
                                                                      
                 
                                                                       
                                             
                                             
                                 
                                                                
                   
        
                       
                                                                    
                              
                                                                      
                                                                    
                                                                 
                                                
                                      
                                           
                                                           
                     
                             
                                               
                                               
            
                                               
                                     
                                  
             
                            
                                                             
                                                    
                                             
                                           
                                                     
             

                                                                        
                                                               
                                                           
                                                             
                         
                  
                                                                
                                       
                                      
                                                         
                                                             

                                          

                                                           
                                 
noncomputable def halaszKernel (N : ℕ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ExpSums.e (-(u * Real.log n))

                                                                    
                                                                       
                          
                                                         
                                                              
                                                               
                                                     
                                                       
                                                
                                                        
                                
                        
                                                     
                                 
           
              
                                                    
                                                             
                                            
                   
                            
                                                
              

                                                            
                                                                  
                                                                      
                            
theorem norm_sum_e_neg_log_Ico_le_vdc_sharp (v : ℝ) (A P W : ℕ)
    (hv : 0 < v) (hA : 1 ≤ A) (hAP : A ≤ P) (hW : P + 2 ≤ W) :
    ‖∑ n ∈ Finset.Ico A (P + 1), ExpSums.e (-(v * Real.log n))‖
      ≤ (v / (A : ℝ) + 2)
          * ((17 / 6) / Real.sqrt (v / (W : ℝ) ^ 2) + 1) := by
  let φ : ℕ → ℝ := fun n => -(v * Real.log n)
  let r : ℝ := v / (W : ℝ) ^ 2
  let θ : ℝ := 2 * Real.sqrt r / 3
  have hWR : (0 : ℝ) < W := by
    have : 1 ≤ W := by omega
    exact_mod_cast this
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hr : 0 < r := by
    simp only [r]
    positivity
  have hθ : 0 < θ := by
    simp only [θ]
    positivity
  have hphase2 : ∀ n : ℕ,
      ExpSums.dIter 2 φ n
        = -v * ExpSums.dIter 2 (fun m : ℕ => Real.log m) n := by
    intro n
    have hhom := congrFun
      (ExpSums.dIter_const_mul 2 (-v) (fun m : ℕ => Real.log m)) n
    simpa only [φ, neg_mul] using hhom
  have hsec : ∀ n, A ≤ n → n < P →
      r ≤ (φ (n + 2) - φ (n + 1)) - (φ (n + 1) - φ n) := by
    intro n hn hnp
    have hn1 : 1 ≤ n := le_trans hA hn
    have hsand := (ExpSums.dIter_log_sandwich 1 n hn1).1
    have hnW : n + 2 ≤ W := by omega
    have hnR : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    have hnWR : ((n + 2 : ℕ) : ℝ) ≤ (W : ℝ) := by exact_mod_cast hnW
    have hden : ((n + 2 : ℕ) : ℝ) ^ 2 ≤ (W : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ hnR.le hnWR 2
    have hinv : 1 / (W : ℝ) ^ 2 ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos hnR) hden
    have hsand' : 1 / ((n + 2 : ℕ) : ℝ) ^ 2
        ≤ -ExpSums.dIter 2 (fun j : ℕ => Real.log j) n := by
      norm_num at hsand
      rw [show (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 1 + 1 by push_cast; ring]
      simpa only [one_div] using hsand
    have hmul := mul_le_mul_of_nonneg_left (hinv.trans hsand') hv.le
    rw [← ExpSums.dIter_two, hphase2]
    simp only [r]
    calc
      v / (W : ℝ) ^ 2 = v * (1 / (W : ℝ) ^ 2) := by ring
      _ ≤ v * -ExpSums.dIter 2 (fun j : ℕ => Real.log j) n := hmul
      _ = -v * ExpSums.dIter 2 (fun j : ℕ => Real.log j) n := by ring
  have hmono : ∀ n, A ≤ n → n < P →
      φ (n + 1) - φ n ≤ φ (n + 2) - φ (n + 1) := by
    intro n hn hnp
    have hs := hsec n hn hnp
    have := hr.le
    linarith
  have hlogA : Real.log ((A + 1 : ℕ) : ℝ) - Real.log (A : ℝ)
      ≤ 1 / (A : ℝ) := by
    have hlog := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < ((A + 1 : ℕ) : ℝ) / A by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at hlog
    have hsub : (((A + 1 : ℕ) : ℝ) / A - 1) = 1 / (A : ℝ) := by
      push_cast
      field_simp
      ring
    rw [hsub] at hlog
    exact hlog
  have hlogP0 : 0 ≤ Real.log ((P + 1 : ℕ) : ℝ) - Real.log (P : ℝ) := by
    have hP1 : 1 ≤ P := le_trans hA hAP
    exact sub_nonneg.mpr (Real.log_le_log (by positivity) (by exact_mod_cast (show P ≤ P + 1 by omega)))
  have hD : (φ (P + 1) - φ P) - (φ (A + 1) - φ A) ≤ v / A := by
    have hdiff : (φ (P + 1) - φ P) - (φ (A + 1) - φ A)
        = v * ((Real.log ((A + 1 : ℕ) : ℝ) - Real.log (A : ℝ))
          - (Real.log ((P + 1 : ℕ) : ℝ) - Real.log (P : ℝ))) := by
      simp only [φ]
      ring
    rw [hdiff]
    have hinner : (Real.log ((A + 1 : ℕ) : ℝ) - Real.log (A : ℝ))
          - (Real.log ((P + 1 : ℕ) : ℝ) - Real.log (P : ℝ))
        ≤ 1 / (A : ℝ) := by linarith
    calc
      v * ((Real.log ((A + 1 : ℕ) : ℝ) - Real.log (A : ℝ))
            - (Real.log ((P + 1 : ℕ) : ℝ) - Real.log (P : ℝ)))
          ≤ v * (1 / (A : ℝ)) := mul_le_mul_of_nonneg_left hinner hv.le
      _ = v / A := by ring
  have hvdc := ExpSums.vdc2 (φ := φ) (θ := θ) (r := r)
    (D := v / A) hθ hr hAP hmono hsec hD
  refine hvdc.trans_eq ?_
  have hrsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  have hrs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hfactor : (2 * θ / r + 1) + 1 / θ
      = (17 / 6) / Real.sqrt r + 1 := by
    simp only [θ]
    field_simp
    nlinarith
  rw [hfactor]

/-- The convenient dyadic-block form of the second-difference estimate.
The side condition `v < (M+1)²` starts exactly where the trivial estimate
ceases to be useful. -/
theorem norm_sum_e_neg_log_Ioc_le_vdc (v : ℝ) (M P : ℕ)
    (hv : 0 < v) (hM : 1 ≤ M) (hMP : M ≤ P) (hP : P ≤ 2 * M)
    (hvM : v < (M + 1 : ℕ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc M P, ExpSums.e (-(v * Real.log n))‖
      ≤ 7 * Real.sqrt v + 12 * (M + 1 : ℕ) / Real.sqrt v + 2 := by
  have hIoc : Finset.Ioc M P = Finset.Ico (M + 1) (P + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc]
  have hA : 1 ≤ M + 1 := by omega
  by_cases hPM : P = M
  · subst P
    simp
    positivity
  have hAP : M + 1 ≤ P := by
    omega
  have hraw := norm_sum_e_neg_log_Ico_le_vdc_sharp v (M + 1) P (2 * (M + 1))
    hv hA hAP (by omega)
  refine hraw.trans ?_
  have hMR : (0 : ℝ) < (M + 1 : ℕ) := by positivity
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hss : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv.le
  have hsqrt : Real.sqrt (v / ((2 * (M + 1) : ℕ) : ℝ) ^ 2)
      = Real.sqrt v / (2 * (M + 1 : ℕ)) := by
    rw [Real.sqrt_div hv.le, Real.sqrt_sq]
    · push_cast
      ring
    · positivity
  rw [hsqrt]
  have hsM : Real.sqrt v < (M + 1 : ℕ) := by
    have hs2 := Real.sq_sqrt hv.le
    push_cast at hvM ⊢
    nlinarith
  have hratio : v / (M + 1 : ℕ) ≤ Real.sqrt v := by
    apply (div_le_iff₀ hMR).mpr
    calc
      v = Real.sqrt v * Real.sqrt v := hss.symm
      _ ≤ Real.sqrt v * (M + 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hsM.le hs.le
  have hsne : Real.sqrt v ≠ 0 := ne_of_gt hs
  have hMRne : ((M + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hMR
  have hsep : (17 / 6) / (Real.sqrt v / (2 * (M + 1 : ℕ)))
      = (17 / 3) * (M + 1 : ℕ) / Real.sqrt v := by
    field_simp
    ring
  rw [hsep]
  have hexpand : (v / (M + 1 : ℕ) + 2)
        * ((17 / 3) * (M + 1 : ℕ) / Real.sqrt v + 1)
      = (17 / 3) * Real.sqrt v + v / (M + 1 : ℕ)
          + (34 / 3) * (M + 1 : ℕ) / Real.sqrt v + 2 := by
    field_simp
    nlinarith
  rw [hexpand]
  have hAs0 : 0 ≤ (M + 1 : ℕ) / Real.sqrt v := by positivity
  ring_nf at hratio hAs0 ⊢
  nlinarith

/-- Kusmin–Landau on a dyadic logarithmic block once its lower endpoint
is beyond `13v/12`.  The separation parameter `v/(12(M+1))` leaves a
small overlap with the second-difference range. -/
theorem norm_sum_e_neg_log_Ioc_le_kusmin (v : ℝ) (M P : ℕ)
    (hv : 0 < v) (hM : 1 ≤ M) (hMP : M ≤ P) (hP : P ≤ 2 * M)
    (hlarge : 13 * v ≤ 12 * (M + 1 : ℕ)) :
    ‖∑ n ∈ Finset.Ioc M P, ExpSums.e (-(v * Real.log n))‖
      ≤ 12 * (M + 1 : ℕ) / v := by
  have hIoc : Finset.Ioc M P = Finset.Ico (M + 1) (P + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc]
  by_cases hPM : P = M
  · subst P
    simp
    positivity
  have hAP : M + 1 ≤ P := by omega
  let θ : ℝ := v / (12 * (M + 1 : ℕ))
  have hMR : (0 : ℝ) < (M + 1 : ℕ) := by positivity
  have hθ : 0 < θ := by
    simp only [θ]
    positivity
  have hlogLower : ∀ n : ℕ, M + 1 ≤ n → n ≤ P →
      1 / (2 * (M + 1 : ℕ) : ℝ)
        ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
    intro n hn hnp
    have hn1 : 1 ≤ n := by omega
    have hlo := ExpSums.log_sub_log_ge n (n + 1) hn1 (by omega)
    have hn20 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have h2M0 : (0 : ℝ) < 2 * (M + 1 : ℕ) := by positivity
    have hn2M : (n + 1 : ℕ) ≤ 2 * (M + 1) := by omega
    have hfrac : 1 / (2 * (M + 1 : ℕ) : ℝ) ≤ 1 / (n + 1 : ℕ) := by
      exact one_div_le_one_div_of_le hn20 (by exact_mod_cast hn2M)
    have hcast : (((n + 1 : ℕ) : ℝ) - n) / (n + 1 : ℕ)
        = 1 / (n + 1 : ℕ) := by
      push_cast
      field_simp
      ring
    rw [hcast] at hlo
    exact hfrac.trans hlo
  have hlogUpper : ∀ n : ℕ, M + 1 ≤ n → n ≤ P →
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)
        ≤ 1 / (M + 1 : ℕ) := by
    intro n hn _hnp
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hnM0 : (0 : ℝ) < (M + 1 : ℕ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / n by positivity)
    have hdivlog : Real.log (((n + 1 : ℕ) : ℝ) / n)
        = Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
      rw [Real.log_div (by positivity) (by positivity)]
    rw [hdivlog] at hlog
    have hsub : (((n + 1 : ℕ) : ℝ) / n - 1) = 1 / n := by
      push_cast
      field_simp
      ring
    rw [hsub] at hlog
    have hfrac : 1 / (n : ℝ) ≤ 1 / (M + 1 : ℕ) := by
      exact one_div_le_one_div_of_le hnM0 (by exact_mod_cast hn)
    exact hlog.trans hfrac
  have hlo : ∀ n, M + 1 ≤ n → n ≤ P →
      ((-1 : ℤ) : ℝ) + θ
        ≤ -(v * Real.log (n + 1)) - -(v * Real.log n) := by
    intro n hn hnp
    have hu := hlogUpper n hn hnp
    have hθdef : θ = v / (12 * (M + 1 : ℕ)) := rfl
    have hvM : v / (M + 1 : ℕ) + v / (12 * (M + 1 : ℕ)) ≤ 1 := by
      field_simp
      nlinarith
    push_cast at hvM
    rw [hθdef]
    have hm := mul_le_mul_of_nonneg_left hu hv.le
    push_cast at hm ⊢
    have hinc : -(v * Real.log ((n : ℝ) + 1))
          - -(v * Real.log (n : ℝ))
        = -v * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
      ring
    rw [hinc]
    have hm' : v * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
        ≤ v / ((M : ℝ) + 1) := by
      calc
        v * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
            ≤ v * (1 / ((M : ℝ) + 1)) := hm
        _ = v / ((M : ℝ) + 1) := by ring
    calc
      -1 + v / (12 * ((M : ℝ) + 1))
          ≤ -(v / ((M : ℝ) + 1)) := by linarith
      _ ≤ -v * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
        linarith
  have hhi : ∀ n, M + 1 ≤ n → n ≤ P →
      -(v * Real.log (n + 1)) - -(v * Real.log n)
        ≤ ((-1 : ℤ) : ℝ) + 1 - θ := by
    intro n hn hnp
    have hl := hlogLower n hn hnp
    have hθdef : θ = v / (12 * (M + 1 : ℕ)) := rfl
    have hm := mul_le_mul_of_nonneg_left hl hv.le
    rw [hθdef]
    push_cast at hm ⊢
    have hinc : -(v * Real.log ((n : ℝ) + 1))
          - -(v * Real.log (n : ℝ))
        = -v * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
      ring
    rw [hinc]
    have hquarter : v / (12 * ((M : ℝ) + 1))
        ≤ v / (2 * ((M : ℝ) + 1)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    have hm' : v / (12 * ((M : ℝ) + 1))
        ≤ v * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
      refine hquarter.trans ?_
      calc
        v / (2 * ((M : ℝ) + 1))
            = v * (1 / (2 * ((M : ℝ) + 1))) := by ring
        _ ≤ v * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := hm
    linarith
  have hmono : ∀ n, M + 1 ≤ n → n < P →
      -(v * Real.log (n + 1)) - -(v * Real.log n)
        ≤ -(v * Real.log (n + 2)) - -(v * Real.log (n + 1)) := by
    intro n hn _hnp
    have hn1 : 1 ≤ n := by omega
    have hsand := (ExpSums.dIter_log_sandwich 1 n hn1).1
    have hd2 : ExpSums.dIter 2 (fun m : ℕ => Real.log m) n ≤ 0 := by
      norm_num at hsand ⊢
      have hnonneg : 0 ≤ (((n : ℝ) + 1 + 1) ^ 2)⁻¹ := by positivity
      nlinarith
    rw [ExpSums.dIter_two] at hd2
    have hm := mul_nonneg hv.le (neg_nonneg.mpr hd2)
    push_cast at hd2 ⊢
    nlinarith
  have hkl := ExpSums.kusmin_landau_shift (φ := fun n : ℕ => -(v * Real.log n))
    (θ := θ) (M := M + 1) (N := P) (-1) hθ hAP
      (by simpa only [Nat.cast_add, Nat.cast_one] using hlo)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hhi)
      (by simpa only [Nat.cast_add, Nat.cast_one] using! hmono)
  refine hkl.trans_eq ?_
  simp only [θ]
  field_simp

private theorem hm_sum_dyadic_tiling {A : Type*} [AddCommMonoid A]
    (V N J : ℕ) (f : ℕ → A) :
    ∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (min (2 ^ j * V) N) (min (2 ^ (j + 1) * V) N), f n
      = ∑ n ∈ Finset.Ioc (min V N) (min (2 ^ J * V) N), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    have h₁ : min V N ≤ min (2 ^ J * V) N := by
      refine min_le_min ?_ le_rfl
      calc
        V = 1 * V := (one_mul V).symm
        _ ≤ 2 ^ J * V := Nat.mul_le_mul_right V Nat.one_le_two_pow
    have h₂ : min (2 ^ J * V) N ≤ min (2 ^ (J + 1) * V) N := by
      refine min_le_min ?_ le_rfl
      exact Nat.mul_le_mul_right V
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))
    exact Finset.sum_Ioc_consecutive f h₁ h₂

/-- The number of binary blocks through `N` is bounded using the numerical
lower bound `log 2 > 2/3`. -/
theorem natLog2_succ_le_three_halves_log_two_mul (N : ℕ) (hN : 1 ≤ N) :
    (((N.log2 + 1 : ℕ) : ℝ)) ≤ (3 / 2 : ℝ) * Real.log (2 * N) := by
  have hN0 : N ≠ 0 := by omega
  have hpowNat : 2 ^ N.log2 ≤ N := Nat.log2_self_le hN0
  have hpow : (2 : ℝ) ^ N.log2 ≤ (N : ℝ) := by exact_mod_cast hpowNat
  have hlogpow : (N.log2 : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h
  have hlogmul : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hJ0 : (0 : ℝ) ≤ (N.log2 + 1 : ℕ) := Nat.cast_nonneg _
  have hJlog : ((N.log2 + 1 : ℕ) : ℝ) * Real.log 2
      ≤ Real.log (2 * (N : ℝ)) := by
    rw [hlogmul]
    push_cast
    nlinarith
  have htwoThird : (2 / 3 : ℝ) * ((N.log2 + 1 : ℕ) : ℝ)
      ≤ Real.log (2 * (N : ℝ)) := by
    calc
      (2 / 3 : ℝ) * ((N.log2 + 1 : ℕ) : ℝ)
          ≤ Real.log 2 * ((N.log2 + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hlog2.le hJ0
      _ = ((N.log2 + 1 : ℕ) : ℝ) * Real.log 2 := mul_comm _ _
      _ ≤ Real.log (2 * (N : ℝ)) := hJlog
  nlinarith

                                                                   
                                                            
                         
                              
                                                     
                                                              
             
                 
        
                                           
                                                                          
                                
                                   
                                                                      
         
                                                                         
                                                           
                                        
                                                
            
                                                                    
                                                                         
                          
                                                         
                                                        
           

                                                                   
                                                                  
                                                   
private theorem sum_two_pow_add_one_range_le_five_halves (N : ℕ)
    (hN : 1 ≤ N) :
    ∑ j ∈ Finset.range (N.log2 + 1), (((2 ^ j + 1 : ℕ) : ℝ))
      ≤ (5 / 2 : ℝ) * (N : ℝ) := by
  have hN0 : N ≠ 0 := by omega
  have hpow0 : 2 ^ N.log2 ≤ N := Nat.log2_self_le hN0
  have htwoLog : 2 * N.log2 ≤ 2 ^ N.log2 := by
    by_cases hk0 : N.log2 = 0
    · simp [hk0]
    have hk1 : 1 ≤ N.log2 := Nat.one_le_iff_ne_zero.mpr hk0
    have htwoPow : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ 2 ^ k := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [pow_succ]
        have hkpow : k + 1 ≤ 2 ^ k := by omega
        omega
    exact htwoPow N.log2 hk1
  have hJNat : 2 * (N.log2 + 1) ≤ N + 2 := by omega
  have hJ : 2 * (((N.log2 + 1 : ℕ) : ℝ)) ≤ (N : ℝ) + 2 := by
    exact_mod_cast hJNat
  have hpow : (2 : ℝ) ^ (N.log2 + 1) ≤ 2 * (N : ℝ) := by
    rw [pow_succ]
    have : (2 : ℝ) ^ N.log2 ≤ (N : ℝ) := by exact_mod_cast hpow0
    nlinarith
  have hgeom : ∑ j ∈ Finset.range (N.log2 + 1), (2 : ℝ) ^ j
      = (2 : ℝ) ^ (N.log2 + 1) - 1 := by
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    norm_num
  simp_rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [Finset.sum_add_distrib, hgeom, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  nlinarith

/-- Every dyadic block is either in the second-difference range or in
the Kusmin–Landau tail.  This combined form is convenient for summing all
blocks without exposing the case split to callers. -/
theorem norm_sum_e_neg_log_dyadic_block_le (v : ℝ) (M P : ℕ)
    (hv : 1 ≤ v) (hM : 1 ≤ M) (hMP : M ≤ P) (hP : P ≤ 2 * M) :
    ‖∑ n ∈ Finset.Ioc M P, ExpSums.e (-(v * Real.log n))‖
      ≤ 22 * Real.sqrt v + 12 * (M + 1 : ℕ) / v := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have hs1 : 1 ≤ Real.sqrt v := by
    have := Real.sqrt_le_sqrt hv
    simpa using this
  by_cases hlarge : 13 * v ≤ 12 * (M + 1 : ℕ)
  · have hkl := norm_sum_e_neg_log_Ioc_le_kusmin v M P hv0 hM hMP hP hlarge
    exact hkl.trans (le_add_of_nonneg_left (by positivity))
  · have hsmall : 12 * ((M + 1 : ℕ) : ℝ) < 13 * v := by
      push_neg at hlarge
      exact hlarge
    by_cases hvM : v < (M + 1 : ℕ) ^ 2
    · have hvdc := norm_sum_e_neg_log_Ioc_le_vdc v M P hv0 hM hMP hP hvM
      refine hvdc.trans ?_
      have hss : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0.le
      have hAs : 12 * ((M + 1 : ℕ) : ℝ) / Real.sqrt v
          ≤ 13 * Real.sqrt v := by
        apply (div_le_iff₀ hs).mpr
        rw [mul_assoc, hss]
        exact hsmall.le
      have hbase : 7 * Real.sqrt v
            + 12 * ((M + 1 : ℕ) : ℝ) / Real.sqrt v + 2
          ≤ 22 * Real.sqrt v := by
        nlinarith
      exact hbase.trans (le_add_of_nonneg_right (by positivity))
    · have hvM' : (((M + 1 : ℕ) : ℝ) ^ 2) ≤ v := by
        push_neg at hvM
        exact hvM
      have hA0 : (0 : ℝ) ≤ (M + 1 : ℕ) := by positivity
      have hAs : ((M + 1 : ℕ) : ℝ) ≤ Real.sqrt v :=
        (Real.le_sqrt hA0 hv0.le).mpr hvM'
      have htriv := ExpSums.norm_sum_e_le_card (Finset.Ioc M P)
        (fun n : ℕ => -(v * Real.log n))
      rw [Nat.card_Ioc] at htriv
      have hcardNat : P - M ≤ M := by omega
      have hcard : (((P - M : ℕ) : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hcardNat
      have hMAs : (M : ℝ) ≤ (M + 1 : ℕ) := by push_cast; linarith
      refine htriv.trans ?_
      have : (((P - M : ℕ) : ℝ)) ≤ Real.sqrt v := hcard.trans (hMAs.trans hAs)
      nlinarith [show 0 ≤ 12 * ((M + 1 : ℕ) : ℝ) / v by positivity]

/-- A dyadic block with its van der Corput cost exposed.  Once the
Kusmin–Landau threshold holds, the square-root term disappears. -/
theorem norm_sum_e_neg_log_dyadic_block_le_split (v : ℝ) (M P : ℕ)
    (hv : 1 ≤ v) (hM : 1 ≤ M) (hMP : M ≤ P) (hP : P ≤ 2 * M) :
    ‖∑ n ∈ Finset.Ioc M P, ExpSums.e (-(v * Real.log n))‖
      ≤ (if 13 * v ≤ 12 * (M + 1 : ℕ) then 0 else 22 * Real.sqrt v)
        + 12 * (M + 1 : ℕ) / v := by
  by_cases hlarge : 13 * v ≤ 12 * (M + 1 : ℕ)
  · simp only [if_pos hlarge, zero_add]
    exact norm_sum_e_neg_log_Ioc_le_kusmin v M P
      (lt_of_lt_of_le zero_lt_one hv) hM hMP hP hlarge
  · simp only [if_neg hlarge]
    exact norm_sum_e_neg_log_dyadic_block_le v M P hv hM hMP hP

/-- If `v ≤ 2T`, only `3(log(2T)+1)/2` binary blocks can lie before
the Kusmin–Landau threshold. -/
theorem card_pre_kusmin_blocks_le (J : ℕ) (v T : ℝ) (hT : 1 ≤ T)
    (hvT : v ≤ 2 * T) :
    (((Finset.range J).filter
        (fun j => 12 * ((2 ^ j + 1 : ℕ) : ℝ) < 13 * v)).card : ℝ)
      ≤ (3 / 2 : ℝ) * (Real.log (2 * T) + 1) := by
  classical
  let B := (Finset.range J).filter
    (fun j => 12 * ((2 ^ j + 1 : ℕ) : ℝ) < 13 * v)
  let Q : ℕ := ⌊13 * T / 6⌋₊
  have hQ1 : 1 ≤ Q := by
    simp only [Q]
    apply Nat.le_floor
    norm_num
    nlinarith
  have hQ0 : Q ≠ 0 := by omega
  have hsub : B ⊆ Finset.range (Q.log2 + 1) := by
    intro j hj
    simp only [B, Finset.mem_filter, Finset.mem_range] at hj
    have hsmall : 12 * (((2 ^ j + 1 : ℕ) : ℝ)) < 13 * v := hj.2
    have hpowR : (((2 ^ j : ℕ) : ℝ)) ≤ 13 * T / 6 := by
      push_cast at hsmall
      have hv13 : 13 * v ≤ 26 * T := by linarith
      have hp : 12 * (((2 ^ j : ℕ) : ℝ)) < 26 * T := by
        push_cast
        nlinarith
      linarith
    have hpowQ : 2 ^ j ≤ Q := by
      simp only [Q]
      exact Nat.le_floor hpowR
    have hjQ : j ≤ Q.log2 := (Nat.le_log2 hQ0).mpr hpowQ
    rw [Finset.mem_range]
    omega
  have hcardNat : B.card ≤ Q.log2 + 1 := by
    have := Finset.card_le_card hsub
    simpa using this
  have hcard : (B.card : ℝ) ≤ ((Q.log2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hQupper : (Q : ℝ) ≤ 13 * T / 6 := by
    simp only [Q]
    exact Nat.floor_le (by positivity)
  have he13 : (13 / 6 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have h2Q : 2 * (Q : ℝ) ≤ Real.exp 1 * (2 * T) := by
    have hm := mul_le_mul_of_nonneg_right he13 (show 0 ≤ 2 * T by linarith)
    nlinarith
  have hlog : Real.log (2 * (Q : ℝ)) ≤ Real.log (2 * T) + 1 := by
    have hraw := Real.log_le_log (show 0 < 2 * (Q : ℝ) by positivity) h2Q
    have hprod : Real.log (Real.exp 1 * (2 * T))
        = Real.log (2 * T) + 1 := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (by positivity),
        Real.log_exp]
      ring
    rwa [hprod] at hraw
  have hQlog := natLog2_succ_le_three_halves_log_two_mul Q hQ1
  change (B.card : ℝ) ≤ (3 / 2 : ℝ) * (Real.log (2 * T) + 1)
  calc
    (B.card : ℝ) ≤ ((Q.log2 + 1 : ℕ) : ℝ) := hcard
    _ ≤ (3 / 2 : ℝ) * Real.log (2 * (Q : ℝ)) := hQlog
    _ ≤ (3 / 2 : ℝ) * (Real.log (2 * T) + 1) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num)

                                                                     
                                                                  
                                                                        
                                
                                                                  
                      
                         
                                                               
           
                      
           
                       
              
                             
                     
                                                         
                               
                 
                                                        
                                                      
                                                  
              
                               
                                                           
                                                                
                                    
                                                           
                                       
                                           
                                       
                                              
                                             
                               
                                                                   
                                                
                                                   
                    
                                              
                                            
                                          
                            
                                 
                                   
                                                                   
                                                                 
              
                                     
                                                           
                                                                 
              
                       
                                                            
                                                
                                           
                                                   
                                           
                                                      
                                                        
                                        
                                                            
                             
                                                                   
                                                            
                                                          
                                              
                                                   
                                                  
                                               
                         
                                
                       
                                                           
                                                       
                                               
             
                          
                                                                  
                              
                                                                             
        
                
                                                                    
                                         
                                     
                                       
                                                             
                                                   
                      
                                                                            
                                                                              
                   
                       
                                         
                                                 
                                    
                                                     
                                  
                
                                        
                                            
            
        
                                
                                                              
                                     
                                                                    
                                      
                                                       
                                    
                       
                  
                          
                                             
                                                                              
                                                           
                                                             
                                                            
                          
             
                                                           
                                                           
                                                      
           

                                                               
                                                                       
                                                                       
                                                             
                      
                           
                                                                 
                                    
                          
                                                                                 
                                        
                    
                                                           
                                            
                                                                  
                                       
                    
                                                                 
                             
               
            
                
                                                

                                 

                                                                
                                                                       
                                         
theorem sum_inv_le_log_of_one_separated {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d : ι → ℝ) (X : ℝ) (hX : 1 ≤ X)
    (hd1 : ∀ i ∈ S, 1 ≤ d i) (hdX : ∀ i ∈ S, d i ≤ X)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |d i - d j|) :
    ∑ i ∈ S, (1 : ℝ) / d i ≤ Real.log X + 1 := by
  classical
  by_cases hS : S = ∅
  · subst S
    simp
    have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
    linarith
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  let k : ι → ℕ := fun i => ⌊d i⌋₊
  have hk1 : ∀ i ∈ S, 1 ≤ k i := by
    intro i hi
    exact Nat.le_floor (by exact_mod_cast hd1 i hi)
  have hkX : ∀ i ∈ S, k i ≤ ⌊X⌋₊ := by
    intro i hi
    exact Nat.floor_le_floor (hdX i hi)
  have hkinj : Set.InjOn k ↑S := by
    intro i hi j hj hij
    have hiS := Finset.mem_coe.mp hi
    have hjS := Finset.mem_coe.mp hj
    have hdi0 : 0 ≤ d i := le_trans (by norm_num) (hd1 i hiS)
    have hdj0 : 0 ≤ d j := le_trans (by norm_num) (hd1 j hjS)
    have hki : ((k i : ℕ) : ℝ) ≤ d i := Nat.floor_le hdi0
    have hkj : ((k j : ℕ) : ℝ) ≤ d j := Nat.floor_le hdj0
    have hik : d i < (k i : ℕ) + 1 := Nat.lt_floor_add_one _
    have hjk : d j < (k j : ℕ) + 1 := Nat.lt_floor_add_one _
    have hfloor : ((k i : ℕ) : ℝ) = (k j : ℕ) := by exact_mod_cast hij
    have habs : |d i - d j| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    by_contra hne
    exact (not_lt_of_ge (hsep i hiS j hjS hne)) habs
  have hpoint : ∀ i ∈ S, (1 : ℝ) / d i ≤ 1 / (k i : ℝ) := by
    intro i hi
    have hkpos : (0 : ℝ) < k i := by exact_mod_cast hk1 i hi
    exact one_div_le_one_div_of_le hkpos
      (Nat.floor_le (le_trans (by norm_num) (hd1 i hi)))
  have hsub : S.image k ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    exact Finset.mem_Icc.mpr ⟨hk1 i hi, hkX i hi⟩
  have hfloor1 : 1 ≤ ⌊X⌋₊ := by
    obtain ⟨i, hi⟩ := hSne
    exact (hk1 i hi).trans (hkX i hi)
  have hfloorX : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := by
    have hX0 : 0 ≤ X := by
      obtain ⟨i, hi⟩ := hSne
      linarith [hd1 i hi, hdX i hi]
    exact Nat.floor_le hX0
  calc
    ∑ i ∈ S, (1 : ℝ) / d i
        ≤ ∑ i ∈ S, (1 : ℝ) / (k i : ℝ) := Finset.sum_le_sum hpoint
    _ = ∑ m ∈ S.image k, (1 : ℝ) / (m : ℝ) :=
      (Finset.sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) hkinj).symm
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (1 : ℝ) / (m : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
    _ ≤ Real.log (⌊X⌋₊ : ℕ) + 1 := ExpSums.sum_inv_le_log ⌊X⌋₊ hfloor1
    _ ≤ Real.log X + 1 := by
      simpa [add_comm] using add_le_add_left
        (Real.log_le_log (by exact_mod_cast hfloor1) hfloorX) 1

/-- Harmonic packing for the points to the left of a fixed member of a
`1`-separated subset of `[-T,T]`. -/
theorem sum_inv_left_of_separated (T : ℝ) (𝒯 : Finset ℝ) (t : ℝ)
    (hT : 1 ≤ T) (ht : t ∈ 𝒯)
    (hrange : ∀ s ∈ 𝒯, |s| ≤ T)
    (hsep : ∀ s ∈ 𝒯, ∀ u ∈ 𝒯, s ≠ u → 1 ≤ |s - u|) :
    ∑ s ∈ 𝒯.filter (fun s => s < t), (1 : ℝ) / (t - s)
      ≤ Real.log (2 * T) + 1 := by
  let S := 𝒯.filter (fun s => s < t)
  apply sum_inv_le_log_of_one_separated S (fun s => t - s) (2 * T) (by linarith)
  · intro s hs
    rw [Finset.mem_filter] at hs
    have hg := hsep t ht s hs.1 (ne_of_gt hs.2)
    rwa [abs_of_pos (sub_pos.mpr hs.2)] at hg
  · intro s hs
    rw [Finset.mem_filter] at hs
    have htR := (abs_le.mp (hrange t ht)).2
    have hsR := (abs_le.mp (hrange s hs.1)).1
    linarith
  · intro s hs u hu hsu
    rw [Finset.mem_filter] at hs hu
    have hg := hsep u hu.1 s hs.1 hsu.symm
    simpa [sub_sub_sub_cancel_right] using hg

/-- Harmonic packing for the points to the right of a fixed member of a
`1`-separated subset of `[-T,T]`. -/
theorem sum_inv_right_of_separated (T : ℝ) (𝒯 : Finset ℝ) (t : ℝ)
    (hT : 1 ≤ T) (ht : t ∈ 𝒯)
    (hrange : ∀ s ∈ 𝒯, |s| ≤ T)
    (hsep : ∀ s ∈ 𝒯, ∀ u ∈ 𝒯, s ≠ u → 1 ≤ |s - u|) :
    ∑ s ∈ 𝒯.filter (fun s => t < s), (1 : ℝ) / (s - t)
      ≤ Real.log (2 * T) + 1 := by
  let S := 𝒯.filter (fun s => t < s)
  apply sum_inv_le_log_of_one_separated S (fun s => s - t) (2 * T) (by linarith)
  · intro s hs
    rw [Finset.mem_filter] at hs
    have hg := hsep t ht s hs.1 (ne_of_lt hs.2)
    rwa [abs_of_neg (sub_neg.mpr hs.2), neg_sub] at hg
  · intro s hs
    rw [Finset.mem_filter] at hs
    have hsR := (abs_le.mp (hrange s hs.1)).2
    have htR := (abs_le.mp (hrange t ht)).1
    linarith
  · intro s hs u hu hsu
    rw [Finset.mem_filter] at hs hu
    have hg := hsep s hs.1 u hu.1 hsu
    simpa [sub_sub_sub_cancel_right] using hg

/-- The reciprocal gaps from a point of a `1`-separated subset of
`[-T,T]` have mass at most two harmonic sums. -/
theorem sum_inv_abs_sub_erase_le (T : ℝ) (𝒯 : Finset ℝ) (t : ℝ)
    (hT : 1 ≤ T) (ht : t ∈ 𝒯)
    (hrange : ∀ s ∈ 𝒯, |s| ≤ T)
    (hsep : ∀ s ∈ 𝒯, ∀ u ∈ 𝒯, s ≠ u → 1 ≤ |s - u|) :
    ∑ s ∈ 𝒯.erase t, (1 : ℝ) / |t - s|
      ≤ 2 * (Real.log (2 * T) + 1) := by
  classical
  have hsplit : 𝒯.erase t = 𝒯.filter (fun s => s < t) ∪
      𝒯.filter (fun s => t < s) := by
    ext s
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hs
      rcases lt_or_gt_of_ne hs.1 with hlt | hgt
      · exact Or.inl ⟨hs.2, hlt⟩
      · exact Or.inr ⟨hs.2, hgt⟩
    · intro hs
      rcases hs with hs | hs
      · exact ⟨ne_of_lt hs.2, hs.1⟩
      · exact ⟨ne_of_gt hs.2, hs.1⟩
  have hdisj : Disjoint (𝒯.filter (fun s => s < t))
      (𝒯.filter (fun s => t < s)) := by
    refine Finset.disjoint_left.mpr fun s hs hu => ?_
    simp only [Finset.mem_filter] at hs hu
    linarith
  rw [hsplit, Finset.sum_union hdisj]
  have hleft : ∑ s ∈ 𝒯.filter (fun s => s < t), (1 : ℝ) / |t - s|
      = ∑ s ∈ 𝒯.filter (fun s => s < t), (1 : ℝ) / (t - s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_filter] at hs
    rw [abs_of_pos (sub_pos.mpr hs.2)]
  have hright : ∑ s ∈ 𝒯.filter (fun s => t < s), (1 : ℝ) / |t - s|
      = ∑ s ∈ 𝒯.filter (fun s => t < s), (1 : ℝ) / (s - t) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_filter] at hs
    rw [abs_of_neg (sub_neg.mpr hs.2), neg_sub]
  rw [hleft, hright]
  linarith [sum_inv_left_of_separated T 𝒯 t hT ht hrange hsep,
    sum_inv_right_of_separated T 𝒯 t hT ht hrange hsep]

/-- The square-root gaps in `[-T,T]` are bounded termwise by `√(2T)`. -/
theorem sum_sqrt_abs_sub_erase_le (T : ℝ) (𝒯 : Finset ℝ) (t : ℝ)
    (ht : t ∈ 𝒯)
    (hrange : ∀ s ∈ 𝒯, |s| ≤ T) :
    ∑ s ∈ 𝒯.erase t, Real.sqrt |t - s|
      ≤ (𝒯.card : ℝ) * Real.sqrt (2 * T) := by
  classical
  have hpoint : ∀ s ∈ 𝒯.erase t,
      Real.sqrt |t - s| ≤ Real.sqrt (2 * T) := by
    intro s hs
    have hsT : s ∈ 𝒯 := Finset.mem_of_mem_erase hs
    apply Real.sqrt_le_sqrt
    have htlo := (abs_le.mp (hrange t ht)).1
    have hthi := (abs_le.mp (hrange t ht)).2
    have hslo := (abs_le.mp (hrange s hsT)).1
    have hshi := (abs_le.mp (hrange s hsT)).2
    rw [abs_le]
    constructor <;> linarith
  calc
    ∑ s ∈ 𝒯.erase t, Real.sqrt |t - s|
        ≤ ∑ _s ∈ 𝒯.erase t, Real.sqrt (2 * T) :=
          Finset.sum_le_sum hpoint
    _ = ((𝒯.erase t).card : ℝ) * Real.sqrt (2 * T) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (𝒯.card : ℝ) * Real.sqrt (2 * T) := by
      have hc : (𝒯.erase t).card ≤ 𝒯.card :=
        Finset.card_le_card (Finset.erase_subset _ _)
      have hcR : ((𝒯.erase t).card : ℝ) ≤ (𝒯.card : ℝ) := by
        exact_mod_cast hc
      exact mul_le_mul_of_nonneg_right hcR (Real.sqrt_nonneg _)

/-- The diagonal logarithmic kernel has exactly `N` terms. -/
theorem norm_halaszKernel_zero (N : ℕ) :
    ‖halaszKernel N 0‖ = (N : ℝ) := by
  rw [halaszKernel]
  simp [ExpSums.e, Nat.card_Icc]

                                                                   
                                                                     
                                                                
                                                                   
                                     
                               
                                                    
                                     
                                                       
                             
                                                                      
           
                                      
                          
                        
             
               
                                              
                                                
                                   
                    
              
                                                       
                                        
                              
                              
                                                                     
              
                                                  
                          
                                                  
                                    
                                                             
                                                          
                                                            
                                                   
                                       
                                               
                                                
                                                            
                         
                                                   
                                                     
                                                       
                         
                                                   
        
                      
                                                               
                                 
                                                                    
                               
                                                    
                                                       
                                           
                                                                            
                    
                                                              
                                                       
                                                       
                                                               
                                                         
                                              
                                                 
                                                          
                           
                                                                  
                                                      
                                                            
                                             
                             
                                                                      
                           
                               
             
                                                 
                                
                                                         
                 
                                            
                    
          

                                      

                                                                        
                                                                    
                                                                
             
theorem norm_halaszKernel_of_one_le_of_le_two_mul (N : ℕ) (v T : ℝ)
    (hv : 1 ≤ v) (hvT : v ≤ 2 * T) (hT : 1 ≤ T) :
    ‖halaszKernel N v‖
      ≤ 1 + 30 * (N : ℝ) / v
        + 33 * Real.sqrt v * (Real.log (2 * T) + 1) := by
  classical
  by_cases hN0 : N = 0
  · subst N
    simp [halaszKernel]
    have hlog : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
    have hterm : 0 ≤ 33 * Real.sqrt v * (Real.log (2 * T) + 1) := by
      positivity
    linarith
  have hN : 1 ≤ N := by omega
  let J := N.log2 + 1
  let f : ℕ → ℂ := fun n => ExpSums.e (-(v * Real.log n))
  let B := (Finset.range J).filter
    (fun j => 12 * (((2 ^ j + 1 : ℕ) : ℝ)) < 13 * v)
  have hpowlt : N < 2 ^ J := by
    simp only [J]
    exact (Nat.log2_lt hN0).mp (Nat.lt_succ_self N.log2)
  have hpowle : 2 ^ N.log2 ≤ N := Nat.log2_self_le hN0
  have hMj : ∀ j ∈ Finset.range J, 2 ^ j ≤ N := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjle : j ≤ N.log2 := by simp only [J] at hj; omega
    exact (Nat.pow_le_pow_right (by norm_num) hjle).trans hpowle
  have htile : ∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n
      = ∑ n ∈ Finset.Ioc 1 N, f n := by
    have ht := hm_sum_dyadic_tiling 1 N J f
    have hleft : (∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc (min (2 ^ j * 1) N)
              (min (2 ^ (j + 1) * 1) N), f n)
        = ∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [mul_one, mul_one, min_eq_left (hMj j hj)]
    rw [hleft] at ht
    have hmin1 : min 1 N = 1 := min_eq_left hN
    have hminN : min (2 ^ J * 1) N = N := by
      rw [mul_one, min_eq_right hpowlt.le]
    rwa [hmin1, hminN] at ht
  have hkernel : halaszKernel N v
      = f 1 + ∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n := by
    rw [halaszKernel, Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons,
      ← htile]
  have hblock : ∀ j ∈ Finset.range J,
      ‖∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n‖
        ≤ (if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
            then 0 else 22 * Real.sqrt v)
          + 12 * (((2 ^ j + 1 : ℕ) : ℝ)) / v := by
    intro j hj
    have hM := hMj j hj
    have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ']
    have hMP : 2 ^ j ≤ min (2 ^ (j + 1)) N := by
      exact le_min (by rw [hpow]; omega) hM
    have hP : min (2 ^ (j + 1)) N ≤ 2 * 2 ^ j := by
      exact (min_le_left _ _).trans_eq hpow
    exact norm_sum_e_neg_log_dyadic_block_le_split v (2 ^ j)
      (min (2 ^ (j + 1)) N) hv Nat.one_le_two_pow hMP hP
  have hsumNorm : ‖∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n‖
      ≤ ∑ j ∈ Finset.range J,
          ((if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
              then 0 else 22 * Real.sqrt v)
            + 12 * (((2 ^ j + 1 : ℕ) : ℝ)) / v) := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hblock)
  have hBsum : ∑ j ∈ Finset.range J,
        (if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
          then 0 else 22 * Real.sqrt v)
      = 22 * Real.sqrt v * (B.card : ℝ) := by
    calc
      ∑ j ∈ Finset.range J,
          (if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
            then 0 else 22 * Real.sqrt v)
          = ∑ j ∈ B, 22 * Real.sqrt v := by
              simp only [B, Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro j _
              by_cases h : 12 * (((2 ^ j + 1 : ℕ) : ℝ)) < 13 * v
              · have hn : ¬ 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ)) :=
                  not_le.mpr h
                push_cast at h hn ⊢
                rw [if_neg hn, if_pos h]
              · have hl : 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ)) :=
                  le_of_not_gt h
                push_cast at h hl ⊢
                rw [if_pos hl, if_neg h]
      _ = 22 * Real.sqrt v * (B.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have htailSum : ∑ j ∈ Finset.range J,
        12 * (((2 ^ j + 1 : ℕ) : ℝ)) / v
      = (12 / v) * ∑ j ∈ Finset.range J,
          (((2 ^ j + 1 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsumForm : ∑ j ∈ Finset.range J,
          ((if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
              then 0 else 22 * Real.sqrt v)
            + 12 * (((2 ^ j + 1 : ℕ) : ℝ)) / v)
      = 22 * Real.sqrt v * (B.card : ℝ)
          + (12 / v) * ∑ j ∈ Finset.range J,
              (((2 ^ j + 1 : ℕ) : ℝ)) := by
    rw [Finset.sum_add_distrib, hBsum, htailSum]
  have hBcard : (B.card : ℝ)
      ≤ (3 / 2 : ℝ) * (Real.log (2 * T) + 1) := by
    simpa only [B] using card_pre_kusmin_blocks_le J v T hT hvT
  have hroot : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  have hpre : 22 * Real.sqrt v * (B.card : ℝ)
      ≤ 33 * Real.sqrt v * (Real.log (2 * T) + 1) := by
    have h := mul_le_mul_of_nonneg_left hBcard
      (show 0 ≤ 22 * Real.sqrt v by positivity)
    nlinarith
  have hA := sum_two_pow_add_one_range_le_five_halves N hN
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have htail : (12 / v) *
        (∑ j ∈ Finset.range (N.log2 + 1), (((2 ^ j + 1 : ℕ) : ℝ)))
      ≤ 30 * (N : ℝ) / v := by
    have h := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 12 / v)
    calc
      (12 / v) *
          (∑ j ∈ Finset.range (N.log2 + 1), (((2 ^ j + 1 : ℕ) : ℝ)))
          ≤ (12 / v) * ((5 / 2 : ℝ) * (N : ℝ)) := h
      _ = 30 * (N : ℝ) / v := by ring
  rw [hkernel]
  refine (norm_add_le _ _).trans ?_
  have hf1 : ‖f 1‖ = 1 := ExpSums.norm_e _
  rw [hf1]
  calc
    1 + ‖∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n‖
        ≤ 1 + ∑ j ∈ Finset.range J,
            ((if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
                then 0 else 22 * Real.sqrt v)
              + 12 * (((2 ^ j + 1 : ℕ) : ℝ)) / v) :=
          add_le_add le_rfl hsumNorm
    _ = 1 + 22 * Real.sqrt v * (B.card : ℝ)
          + (12 / v) * ∑ j ∈ Finset.range J,
              (((2 ^ j + 1 : ℕ) : ℝ)) := by rw [hsumForm]; ring
    _ ≤ 1 + 30 * (N : ℝ) / v
          + 33 * Real.sqrt v * (Real.log (2 * T) + 1) := by
      linarith

/-- The scale-sensitive kernel estimate for a signed frequency. -/
theorem norm_halaszKernel_le_of_abs_le_two_mul (N : ℕ) (u T : ℝ)
    (hu : 1 ≤ |u|) (huT : |u| ≤ 2 * T) (hT : 1 ≤ T) :
    ‖halaszKernel N u‖
      ≤ 1 + 30 * (N : ℝ) / |u|
        + 33 * Real.sqrt |u| * (Real.log (2 * T) + 1) := by
  rcases le_total 0 u with hu0 | hu0
  · rw [abs_of_nonneg hu0]
    exact norm_halaszKernel_of_one_le_of_le_two_mul N u T
      (by simpa [abs_of_nonneg hu0] using hu)
      (by simpa [abs_of_nonneg hu0] using huT) hT
  · rcases hu0.eq_or_lt with rfl | huNeg
    · norm_num at hu
    · have hnorm := ExpSums.norm_sum_e_neg (Finset.Icc 1 N)
          (fun n : ℕ => -(|u| * Real.log n))
      have hconj : ‖halaszKernel N u‖ = ‖halaszKernel N |u|‖ := by
        rw [halaszKernel, halaszKernel]
        rw [← hnorm]
        refine congrArg norm (Finset.sum_congr rfl fun n _ => ?_)
        rw [abs_of_neg huNeg]
        congr 1
        ring
      rw [hconj]
      exact norm_halaszKernel_of_one_le_of_le_two_mul N |u| T hu huT hT

/-- **H-4, the constant `64`.**  The refined kernel ledger closes the
well-spaced row at the exact constant used by the interface. -/
theorem sum_norm_halaszKernel_sub_le_sixty_four (N : ℕ) (T : ℝ)
    (𝒯 : Finset ℝ) (t : ℝ) (hT : 1 ≤ T) (ht : t ∈ 𝒯)
    (hrange : ∀ s ∈ 𝒯, |s| ≤ T)
    (hsep : ∀ s ∈ 𝒯, ∀ u ∈ 𝒯, s ≠ u → 1 ≤ |s - u|) :
    ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
      ≤ 64 * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
        * (Real.log (2 * T) + 1) := by
  classical
  let L := Real.log (2 * T) + 1
  have hlog : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hL1 : 1 ≤ L := by simp only [L]; linarith
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  have hsT1 : 1 ≤ Real.sqrt T := by
    have hs := Real.sqrt_le_sqrt hT
    simpa using hs
  have hsT0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    have hs2sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs20 := Real.sqrt_nonneg 2
    nlinarith
  have hs2T : Real.sqrt (2 * T) ≤ (3 / 2 : ℝ) * Real.sqrt T := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right hs2 hsT0
  have hdiag : ‖halaszKernel N (t - t)‖ = (N : ℝ) := by
    simpa using norm_halaszKernel_zero N
  have hoff : ∀ s ∈ 𝒯.erase t,
      ‖halaszKernel N (t - s)‖
        ≤ 1 + 30 * (N : ℝ) / |t - s| + 33 * Real.sqrt |t - s| * L := by
    intro s hs
    have hsMem : s ∈ 𝒯 := Finset.mem_of_mem_erase hs
    have hne : t ≠ s := ne_comm.mp (Finset.ne_of_mem_erase hs)
    have hgap := hsep t ht s hsMem hne
    have hgapT : |t - s| ≤ 2 * T := by
      have htlo := (abs_le.mp (hrange t ht)).1
      have hthi := (abs_le.mp (hrange t ht)).2
      have hslo := (abs_le.mp (hrange s hsMem)).1
      have hshi := (abs_le.mp (hrange s hsMem)).2
      rw [abs_le]
      constructor <;> linarith
    simpa only [L] using
      norm_halaszKernel_le_of_abs_le_two_mul N (t - s) T hgap hgapT hT
  have hoffsum : ∑ s ∈ 𝒯.erase t, ‖halaszKernel N (t - s)‖
      ≤ ((𝒯.erase t).card : ℝ)
        + 30 * (N : ℝ) * (∑ s ∈ 𝒯.erase t, (1 : ℝ) / |t - s|)
        + 33 * L * (∑ s ∈ 𝒯.erase t, Real.sqrt |t - s|) := by
    refine (Finset.sum_le_sum hoff).trans_eq ?_
    have hA : ∑ s ∈ 𝒯.erase t, 30 * (N : ℝ) / |t - s|
        = 30 * (N : ℝ) *
          (∑ s ∈ 𝒯.erase t, (1 : ℝ) / |t - s|) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    have hB : ∑ s ∈ 𝒯.erase t, 33 * Real.sqrt |t - s| * L
        = 33 * L * (∑ s ∈ 𝒯.erase t, Real.sqrt |t - s|) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_one, hA, hB]
  have hinv := sum_inv_abs_sub_erase_le T 𝒯 t hT ht hrange hsep
  have hsqrt := sum_sqrt_abs_sub_erase_le T 𝒯 t ht hrange
  have hcardNat : (𝒯.erase t).card ≤ 𝒯.card :=
    Finset.card_le_card (Finset.erase_subset _ _)
  have hcard : ((𝒯.erase t).card : ℝ) ≤ (𝒯.card : ℝ) := by
    exact_mod_cast hcardNat
  have hinvScaled := mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ 30 * (N : ℝ) by positivity)
  have hsqrtScaled := mul_le_mul_of_nonneg_left hsqrt
    (show 0 ≤ 33 * L by positivity)
  have hofffinal : ∑ s ∈ 𝒯.erase t, ‖halaszKernel N (t - s)‖
      ≤ (𝒯.card : ℝ) + 60 * (N : ℝ) * L
        + 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T)) := by
    refine hoffsum.trans ?_
    simp only [L] at hinvScaled ⊢
    linarith
  have hsplit : ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
      = ‖halaszKernel N (t - t)‖
        + ∑ s ∈ 𝒯.erase t, ‖halaszKernel N (t - s)‖ := by
    rw [add_comm]
    exact (Finset.sum_erase_add _ _ ht).symm
  have hrow : ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
      ≤ (N : ℝ) + ((𝒯.card : ℝ) + 60 * (N : ℝ) * L
        + 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T))) := by
    rw [hsplit, hdiag]
    linarith
  have hNpart : (N : ℝ) + 60 * (N : ℝ) * L
      ≤ 64 * (N : ℝ) * L := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hL1)]
  have hrootScaled : 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T))
      ≤ (99 / 2 : ℝ) * (𝒯.card : ℝ) * Real.sqrt T * L := by
    have hc0 : (0 : ℝ) ≤ (𝒯.card : ℝ) := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hs2T
      (show 0 ≤ 33 * L * (𝒯.card : ℝ) by positivity)
    nlinarith
  have honeSL : (1 : ℝ) ≤ Real.sqrt T * L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsT1) (sub_nonneg.mpr hL1)]
  have hcardUnit : (𝒯.card : ℝ)
      ≤ (𝒯.card : ℝ) * Real.sqrt T * L := by
    have hc0 : (0 : ℝ) ≤ (𝒯.card : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr honeSL)]
  have hCpart : (𝒯.card : ℝ)
        + 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T))
      ≤ 64 * (𝒯.card : ℝ) * Real.sqrt T * L := by
    linarith
  calc
    ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
        ≤ (N : ℝ) + ((𝒯.card : ℝ) + 60 * (N : ℝ) * L
          + 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T))) := hrow
    _ = ((N : ℝ) + 60 * (N : ℝ) * L)
          + ((𝒯.card : ℝ)
            + 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T))) := by ring
    _ ≤ 64 * (N : ℝ) * L
          + 64 * (𝒯.card : ℝ) * Real.sqrt T * L :=
      add_le_add hNpart hCpart
    _ = 64 * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
          * (Real.log (2 * T) + 1) := by simp only [L]; ring

                                                                    
                                                                  
                                                        
                                       
                                                 
                                  
                                               
                                                     
                                                                      
                                                     
                                    
                                                                 
           
                              
                                                      
                            
                                                                   
                        
                 
              
                       
                                                             
           
                                          
           
             
        
                      
                                     
                                     
                                                                      
              
                           
                              
                                       
                                                              
                                        
                 
                       
                                               
                             
             
          
        
                                     
                                       
                                                              
                                                   
                                                                         
                 
                            
                                                                           
                                                     
                                               
                                                         
             
                                                      
                                                                     
                                                         
                                                    
                                             
           
                                             
              
                                                        
                                                           
                                             
                                       
        
           
      
                                   
                                                            
                                                                  
                                                   
                                  
                                                               
                
                   
          

end MoltResearch

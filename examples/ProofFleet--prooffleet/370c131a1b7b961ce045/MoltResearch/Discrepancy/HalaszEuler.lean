                                               
import MoltResearch.Discrepancy.TruncatedBridge
                                               
import MoltResearch.Discrepancy.ChebyshevTail
import MoltResearch.Discrepancy.MertensFirst
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.SmoothNumbers
import MoltResearch.Discrepancy.SmoothRankin
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Track C: the Euler-product log bridge, upper direction (Track R, C4b-1)

The pointwise Euler input of the Halász leg: for a completely
multiplicative `f` bounded by `1`, just right of the `1`-line,

  `log ‖L_f(s)‖ ≤ ∑'_p Re(f(p) p^{−s}) + 1`.

This is the mirror of `EulerLogBridge.tsum_re_dirichlet_le_log_norm_LSeries`
(which bounds the prime sum *by* the L-norm), generalized from Dirichlet
characters to arbitrary completely multiplicative bounded `f` via Mathlib's
`EulerProduct.exp_tsum_primes_log_eq_tsum`. Both directions share the same
second-order tail: `∑_p ‖log(1−w_p)⁻¹ − w_p‖ ≤ ∑_p p^{−2} ≤ 1`.

Downstream (C4b-2/3): truncation at `y` and Mertens turn this into
`‖L_f(1 + 1/log y − it)‖ ≤ C · (log y) · exp(−D(f, p^{it}; y)²)` — the
Halász-quality pointwise decay on the non-pretentious range, consumed by
the `𝒯₀`-window bound and the `𝒯₁`-mean-square assembly (C4e).
-/

open Complex

namespace MoltResearch

                                                                         
                  
                                               
                                                               
                                                                
                                                                           
                             
           
                    
                  
                  
                                    
                                                  
                                                  
               
                
          
                   
                                                                                    
                                           
                                             
                  

                                                                   
                                                  
                                                         
                                                                             
                                              
                                            
                     
                                                                         
                                                                                      
                             
                             
                                            
                                
                             
                                                                       
                                  
          
                                                                   
                                  
          
                       
                                                                      
                                                                                     
                                                          
                                                
                      
              
                                                
                                                             
              
                                                        
             

                                                                    
                                                               
                                                                    
                                     
                                                              
                                           
                                           
                                                                  
                                                   
                                       
                                                                
           
                                                      
                    
                                                                 
                          
                              
                    
                 
                                        
                   
                                          
                    
                                                  
                                                     
                                             
                                                               
                                                                                        
                           
                                                                              
                                                                              
                            
                                                                           
                                  
                          
                                                                            
                
                             
                                     
                                                            
                                                                           
                
                                    
                                                         
                              
                                        
                                             
                           
                                                                         
                                                                            
                                                  
            
                
                                                        
                      
                                                                 
                                                    
           
                                       
                              
                                                 
                     
           
               
                                                            
                                         
                     
           
                                   
              
                               
                                                                       
           
                     
                                                                      
                                                                       
                                                                          
                                                
          
              
                                                      
                                                    
           
                                 
                                                                         
                                
                                     
                                                                      
                                                                 
                                                             
                                            
                                                   
                                                                         
                         
                                  
                                                             
                                 
                                    
                                         
          
                                                                   
                       
                                  
                                                                      
                                                                      
                           
               
           
                                           
                                                  
                                                            
                                                                                
                                        
                               
                                                                     
           
                                           
                                                        
                     
                                
                                                                              
              
                                                                       
                                                                  
                                                                    
                           
                             
                                       
                     
                                                   
              
                       
                                               
                                                           
                               
                                                                      
                                                                                     
                                                                                  
             
                                                                               
                                                              
                                     
                                      
                                 
                                                        
                                                   
                  
                              
                                              
                                                 
                                           
                                   
                                                                                 
                    
             
                                    
                                                                                      
           
                         
                                                          
                                            
                                                                                      
                                                 
                                                                   
                                     
                                                                    
                                             
                              
                                                                                 
                                                                            
                                                
                                                             
                                                           
                                                                     
                                                                                       
                                               
                         
                      

                                                               
                                                           
                                                                       
                                                                      
                                                       
                                                        
                                                                            
                                  
                                    
                                                         
                                                                                  
           
                                     
                                         
                                               
                                                 
                                 
                                            
                        
                                     
               
                                                            
                                
               
        
                                               
                                                                 
                               
                                                                       
           
                     
                                                                      
                                                                       
                                                                          
                                                
          
              
                                                      
                                                            
                                                                                   
                                                               
                                            
               
                                                                      
                                                    
                                                     
                           
                                   
                                                                 
                                         
               
                                                             
                                      
                                                                                
                                     
               
                                                                 
             
                 
               
          
                            
                       
                                               
                      
                                   
                                            
                                                                       
               
                                      
                                                 
              
                                                                      
                                                                  
                                   
                                                                       
                                   
             
                                        
                                                              
               
                
                                       
                                            
                                                                
                                             
               
                          
                                                                         
                                                          
                                                 
                                                             
                                                                   
                                            
                                                   
                      
                                         
                                       
                                     
                                                      
               
                                                 
                 
                                                                   
                                                                  
                                                                          
                                                
          
                       
              
                                                  
                                                              
                                                                                 
                                   
                                 
                                                                               
                
                                                 
                                      
                        
                                                              
                                                                                   
                                                       
                                               
                                                 
                                                              
                                                     
                                                                                    
            
                                                           
                      
                                                       
                              
                                                                              
                               
                                                                         
                                                           
                                                     
                 
                                                       
                                                                                   
                                                 
                                                                     
                                                        
                                         
                                                     
                                                 
                         
                         
                            
                  
                                                            
                                                          
                                                                              
                                                            
           
               
              
                    
                                                  
                                         
              
              
                                                                                  
                                               
                                                               
                                
                                 
                                                                         
              
                                             
                                                               
                                                                        
                                                           
                                                                          
                              
                        
                                                          
                                            
                                               
                                                 
                                                                                  
           
                                                                 
                                               
                                                 
                                                                                  
           
                                                                 
                                    
                                                      
                                                     
           
                            
                                                
                                                
                                                                          
                                
                                                                                        
                                                                    
                                                
                            
                                                                        
                                                        
                              
                          
                                                                                    
                                   
                                             
                                                                         
             
                              
                               
                                                                 
                                                              
                        
                                    
                
                               
                                                        
                                                                     
                                                                            
                                                                       
                              
                     
                                 
                                              
                       
                                                                 
                            
                                                                      
                                                             
                     
             
                                        
                                                                                     
                   
               
                                          
                                                    
                             
                                                                               
                        
                                                              
                                                                  
                    
            
                                                                                       
                         
                                                                                  
            


                                                              
                                                                      
                                                     
                                                                 
                                                                     
                  
                                                
                                                                            
                                  
                                                                             
                                                                     
                      
                                                                                  
           
                                               
                                           
                                                 
                                                   
                                   
                                                    
            
                                                         
                                   
                                                                
                                                     
               
                                                             
                                                      
                                                                    
                                     
                                        
             
               
          
                                                          
                                                                       
                                     
                                        
             
               
          
                                          
           
                                                              
        
                                                                              
                                          
                                                                             
                                                    
                                              
                                               
                    
        
                                                                           
                                                
                                            
                                                      
                                                        
                                                
                                        
                                        
                                                                                
                
                                                     
                                                  
                                                
                      
              
                                                 
                                                                   
                                    
             
              
                                                      
                                              
                          
                                                                           
                                              
          
                       
                 
                                    
                                                 
                                            
                                                  
                                          
                          
             
                          
                                                                             
                                                                       
           
                                    
             
          
                                                
                                                       
                                                                   
                                                            
                                                                        
                                    
                                                               
                                                
                     
                                                                              
                                       
                                                                                  
                                               
                                                                                  
                   
                                                                                      
                           
               
                                                
                                                        
                   
              
                
                                                                                    
                   
                                                    
                                                        
                                                
                       
                                          
                          
                          
                      
                      
                                                                           
                                       
                                                                   
                       
                                                                      
            
                 
                                                                   
                     
                                                            
                                                                     
             
              
                                                
                                                         
                                                                                
                                                                                      
                          
                                                                                  
                                                    
                                                                 
                                
                                                        
                                             
                                                                                    
                                  
                                                        
                                              
                        
                                                                                 
                          
                                                                       
                        
                                                                                    
                                 


                                       
                                                                        
                                 
                             
                
                                                   
       

                                                                     
                             
                                                             
                                                 
                             
                                                                 
           
                 
            
                                            
                                         
                                               
                                         
                                                        
                                                          
                   
                                          
                                            
                                                            
                                 
                               

                                                                    
                 
                                                                 
             
                     
                                                                 
                                     
           
                          
                                            
                                             
                                           
            
                                               

                                                                      
                                                                     
                                                                    
                                                  
                                                       
                                                      
                                                                        
                                                                  
                                                         
                                                                     
                      
                                                                
                                                                                  
           
                                                                      
               
                                                                
                          
               
              
                  
                                 
                    
                                             
                       
                 
                                 
           
               
              
         
                
          
                                                            
                         
                           
                                                     
                      
                         
                                 
                                                 
                           
                                                    
                                           
                                                                             
           
              
                                            
              
                                                           
                 
                                   
                                              
                                                          
                         
                                                   
                                                      
                                       
           
                             


                                                          
                                                                      
                                                                      
                                                                   
           
                                          
                                                      
                                                                        
                                                          
                                           
                            
                                          
           
                                                                      
               
                                                                  
                   
               
                                                                     
                          
               
              
                  
                                 
                    
                                             
                       
                 
                                 
           
               
              
         
                
          
                             
                    
                                                               
                          
                               
                    
                 
                                        
                           
                                          
                            
                                                  
                                                     
                                             
                                                               
                                      
                                                               
                     
                
                                                              
                     
                
                                                              
                     
                
                            
                                                                           
                                   
              
               
                                                                     
                                                                          
                
                           
                                                              
                                     
           
               
              
         
                
                     
                                
                             
                                                        
                           
                          
                                                                     
                 
                              
                                                     
                                    
                
                                  
                                    
                       
                                             
                             
           
                                                                   
                                                           
                                                                
                      
                                      
                                               
                                     
                        
                                    
           
                                    
                      
                             
                                       
                                               
                                                   
                                                 
                                                              
                                       
                        
                
                 
                
                                            
                                   
                                                 
                                             
                                                      
                                  
                                                        
                                          
                                                                 
                                                                    
                 
                                                              
                  
                        
              
                  
                
                                                         
                       
                                                                 
                                              
              
                                          
                
                                      
                            
                     
                                    
                            
                     
                       
                                                        
                                                     
                               
                                                         
                                                                  
                                                      
                                                           
                            
                                                 
                                                             
                                           
                       
                                     
                            
                                                
                                                             
                                                   
                                                   
                                                 
                                                
                  
                                                     


                                   
                                                                    
                                                                  
                                                                     
                                                                   
                                                               
         
                                                                
                     
                                                                         
                                                
                                                                               
           
                                              
                                                        
                            
               
        
                         
                                                       
              
                                               
                               
               
              
                                                       
                                 
                               
                               
                
                                                     
                                                 
                
                 
                                                     
              
                                                        
                                 
                                                                             
                                             
            
                                                  
              
                      
            
                                 
                                  
                                                         
              
                                      
             
                                     
                                                          
                         
                       
              
                                       
                   
                                                      
                
                                             
                                        
                                              
                         
               
                                                                       
                                                             
                                                 
                                                    
                                                      
                               
                                                                     
                                        
                        
                                                   
              
                                                          
                                              
               
                                    
                         
                                         
                                                           
                                                                
                                                                   
                                                                  
                         
                                                
                                                                               
                            
                                                    
                                            
                                                                              
                                  
                                       
                                                    
                                                     
                                                           
                                                                              
                       
                      
                       
                                           
                                                           
                                        
                                                          
                                     
                      
                     
                                                                        
                                                                   
                                                                
                                                    
                                           
                       
                        
                                                                         
                                              
                      
                                                                     
                                                    
                                                        
                                                                            
                                             
                                                
                     
                       
                  
                                                            
                                                                               
                                             
                                                
                     
                       
                  
                                                           
                                                  
                   
                    
                     
              
                                                             
                                                
                                                      
                                                   
                                
                                                    
                     
                                                    
                                                              
                                                   
                                      
                                                                     
                                 
                                                               
                     
                                                                  
                                            
                          


set_option maxHeartbeats 1600000 in
/-- **The smooth series tail** (Track R, M2-i4a3): truncating the
smooth Dirichlet series on the 1-line at the box `X` costs at most
`X^{−δ}·∏_{p<y}(1−p^{δ−1})⁻¹` for any `δ ∈ (0,1)` — the Rankin
device applied to the tail. -/
theorem norm_smooth_tsum_sub_sum_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    (y X : ℕ) (hX : 1 ≤ X) (s : ℂ) (hs : s.re = 1)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ‖(∑' n : ℕ, (if n ∈ Nat.smoothNumbers y then f n else 0)
          * (if n = 0 then 0 else (n:ℂ)^(-s)))
        - ∑ n ∈ Nat.smoothNumbersUpTo X y,
            (if n ∈ Nat.smoothNumbers y then f n else 0)
              * (if n = 0 then 0 else (n:ℂ)^(-s))‖
      ≤ (X:ℝ)^(-δ) * ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
  classical
  set F : ℕ → ℂ := fun n => (if n ∈ Nat.smoothNumbers y then f n else 0)
    * (if n = 0 then 0 else (n:ℂ)^(-s)) with hF_def
  -- the norm majorant and its summability
  set h : ℕ → ℝ := fun n =>
    if n ∈ Nat.smoothNumbers y then 1/(n:ℝ) else 0 with hh_def
  have hFle : ∀ n, ‖F n‖ ≤ h n := by
    intro n
    rw [hF_def, hh_def]
    dsimp only
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      have h0 : (0:ℕ) ∉ Nat.smoothNumbers y := by
        intro hmem
        exact (Nat.ne_zero_of_mem_smoothNumbers hmem) rfl
      rw [if_neg h0]
      simp
    · rw [if_neg hn, norm_mul]
      have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hnorm : ‖((n:ℕ):ℂ)^(-s)‖ = 1/(n:ℝ) := by
        rw [Complex.norm_natCast_cpow_of_pos hn0,
          show (-s).re = -1 from by rw [Complex.neg_re, hs],
          Real.rpow_neg_one, one_div]
      rw [hnorm]
      by_cases hsm : n ∈ Nat.smoothNumbers y
      · rw [if_pos hsm, if_pos hsm]
        have := hb n
        have h1 : (0:ℝ) ≤ 1/(n:ℝ) := by positivity
        nlinarith [norm_nonneg (f n)]
      · rw [if_neg hsm, if_neg hsm, norm_zero, zero_mul]
  have hh_nonneg : ∀ n, 0 ≤ h n := by
    intro n
    rw [hh_def]
    dsimp only
    split
    · positivity
    · exact le_refl 0
  have hh_sum : Summable h := by
    refine summable_of_sum_le
      (c := ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1:ℝ)))⁻¹)
      hh_nonneg fun u => ?_
    have h1 : ∑ n ∈ u, h n
        ≤ ∑ n ∈ Nat.smoothNumbersUpTo (u.sup id + 1) y, (1:ℝ)/n := by
      rw [hh_def]
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun n _ _ => by positivity)
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [Nat.mem_smoothNumbersUpTo]
      refine ⟨?_, hn.2⟩
      have h2 := Finset.le_sup (f := id) hn.1
      simp only [id_eq] at h2
      omega
    have h2 : ∑ n ∈ Nat.smoothNumbersUpTo (u.sup id + 1) y, (1:ℝ)/n
        ≤ ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1:ℝ)))⁻¹ := by
      have hr := sum_rpow_smoothNumbersUpTo_le 1 (by norm_num) y
        (u.sup id + 1)
      refine le_trans (le_of_eq ?_) hr
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Real.rpow_neg_one, one_div]
    exact le_trans h1 h2
  have hFsum : Summable F :=
    Summable.of_norm (Summable.of_nonneg_of_le
      (fun n => norm_nonneg _) hFle hh_sum)
  -- the split
  have hsplit := hFsum.sum_add_tsum_compl
    (s := Nat.smoothNumbersUpTo X y)
  have hdiff : (∑' n : ℕ, F n) - ∑ n ∈ Nat.smoothNumbersUpTo X y, F n
      = ∑' n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ), F n := by
    linear_combination (hsplit).symm
  rw [hdiff]
  -- bound the complement sum by the Rankin tail
  have hcompl_sum : Summable fun n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ)
      => ‖F n.1‖ := by
    exact (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      hFle hh_sum).subtype _
  refine le_trans (norm_tsum_le_tsum_norm hcompl_sum) ?_
  -- pointwise tail majorant on the complement
  set h' : ℕ → ℝ := fun n =>
    if n ∈ Nat.smoothNumbers y then (X:ℝ)^(-δ) * (n:ℝ)^(δ-1) else 0
    with hh'_def
  have hle' : ∀ n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ),
      ‖F n.1‖ ≤ h' n.1 := by
    rintro ⟨n, hn⟩
    dsimp only
    rw [Set.mem_compl_iff, Finset.mem_coe,
      Nat.mem_smoothNumbersUpTo] at hn
    push_neg at hn
    by_cases hsm : n ∈ Nat.smoothNumbers y
    · have hnX : X < n := by
        by_contra hle
        push_neg at hle
        exact (hn hle) hsm
      have hn1 : 1 ≤ n := by
        have := Nat.ne_zero_of_mem_smoothNumbers hsm
        omega
      refine le_trans (hFle n) ?_
      rw [hh_def, hh'_def]
      dsimp only
      rw [if_pos hsm, if_pos hsm]
      have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
      have hXr : (X:ℝ) ≤ n := by
        exact_mod_cast (by omega : X ≤ n)
      have hX0 : (0:ℝ) < X := by exact_mod_cast hX
      -- 1/n = n^{δ−1}·n^{−δ} ≤ n^{δ−1}·X^{−δ}
      have h1 : (1:ℝ)/(n:ℝ) = (n:ℝ)^(δ-1) * (n:ℝ)^(-δ) := by
        rw [← Real.rpow_add (by linarith)]
        rw [show δ-1 + -δ = -1 from by ring, Real.rpow_neg_one, one_div]
      rw [h1]
      have h2 : (n:ℝ)^(-δ) ≤ (X:ℝ)^(-δ) := by
        exact Real.rpow_le_rpow_of_nonpos hX0 hXr (by linarith)
      calc (n:ℝ)^(δ-1) * (n:ℝ)^(-δ)
          ≤ (n:ℝ)^(δ-1) * (X:ℝ)^(-δ) := by
            refine mul_le_mul_of_nonneg_left h2 ?_
            positivity
        _ = (X:ℝ)^(-δ) * (n:ℝ)^(δ-1) := by ring
    · rw [hh'_def]
      dsimp only
      rw [if_neg hsm]
      have : F n = 0 := by
        rw [hF_def]
        dsimp only
        rw [if_neg hsm, zero_mul]
      rw [this, norm_zero]
  -- the base Rankin-summable and the partial-sum bound
  have hbase_nonneg : ∀ n, 0 ≤ (if n ∈ Nat.smoothNumbers y
      then (n:ℝ)^(δ-1) else 0) := by
    intro n
    split
    · positivity
    · exact le_refl 0
  have hbase_partial : ∀ u : Finset ℕ,
      ∑ n ∈ u, (if n ∈ Nat.smoothNumbers y then (n:ℝ)^(δ-1) else 0)
        ≤ ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
    intro u
    have h1 : ∑ n ∈ u, (if n ∈ Nat.smoothNumbers y then (n:ℝ)^(δ-1) else 0)
        ≤ ∑ n ∈ Nat.smoothNumbersUpTo (u.sup id + 1) y, (n:ℝ)^(-(1-δ)) := by
      rw [← Finset.sum_filter]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun n _ _ => by positivity))
        (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
      · intro n hn
        rw [Finset.mem_filter] at hn
        rw [Nat.mem_smoothNumbersUpTo]
        refine ⟨?_, hn.2⟩
        have h2 := Finset.le_sup (f := id) hn.1
        simp only [id_eq] at h2
        omega
      · congr 1
        ring
    have h2 := sum_rpow_smoothNumbersUpTo_le (1-δ) (by linarith) y
      (u.sup id + 1)
    have h3 : ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1-δ)))⁻¹
        = ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
      refine Finset.prod_congr rfl fun p _ => ?_
      congr 2
      ring
    rw [h3] at h2
    exact le_trans h1 h2
  have hbase_sum : Summable (fun n =>
      if n ∈ Nat.smoothNumbers y then (n:ℝ)^(δ-1) else 0) :=
    summable_of_sum_le hbase_nonneg hbase_partial
  have hh'_sum : Summable h' := by
    refine Summable.congr (hbase_sum.mul_left ((X:ℝ)^(-δ))) fun n => ?_
    rw [hh'_def]
    dsimp only
    split
    · rfl
    · rw [mul_zero]
  -- complement tsum chain
  have hsub_le : (∑' n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ), ‖F n.1‖)
      ≤ ∑' n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ), h' n.1 :=
    Summable.tsum_le_tsum hle' hcompl_sum (hh'_sum.subtype _)
  have hh'_nonneg : ∀ n, 0 ≤ h' n := by
    intro n
    rw [hh'_def]
    dsimp only
    split
    · positivity
    · exact le_refl 0
  have hsub_full : (∑' n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ), h' n.1)
      ≤ ∑' n : ℕ, h' n := by
    rw [show (∑' n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ), h' n.1)
        = ∑' n : ℕ, Set.indicator
            {n : ℕ | n ∉ Nat.smoothNumbersUpTo X y} h' n from
      tsum_subtype _ _]
    refine Summable.tsum_le_tsum (fun n => ?_) (hh'_sum.indicator _) hh'_sum
    by_cases hn : n ∈ {n : ℕ | n ∉ Nat.smoothNumbersUpTo X y}
    · rw [Set.indicator_of_mem hn]
    · rw [Set.indicator_of_notMem hn]
      exact hh'_nonneg n
  have hfull : (∑' n : ℕ, h' n)
      ≤ (X:ℝ)^(-δ) * ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
    refine Real.tsum_le_of_sum_le (fun n => ?_) fun u => ?_
    · rw [hh'_def]
      dsimp only
      split
      · positivity
      · exact le_refl 0
    · rw [hh'_def]
      calc ∑ n ∈ u, (if n ∈ Nat.smoothNumbers y
            then (X:ℝ)^(-δ) * (n:ℝ)^(δ-1) else 0)
          = (X:ℝ)^(-δ) * ∑ n ∈ u, (if n ∈ Nat.smoothNumbers y
              then (n:ℝ)^(δ-1) else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            split
            · rfl
            · rw [mul_zero]
        _ ≤ (X:ℝ)^(-δ) * ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
            refine mul_le_mul_of_nonneg_left (hbase_partial u) ?_
            positivity
  linarith [hsub_le, hsub_full, hfull]


                                   
                                                                   
                                                                   
                                                                 
                                                                   
                                                              
                                                                   
                                                               
                                            
                                                      
                                                                  
                                                        
                                 
                                                             
                                                              
                   
                                                                  
                                                     
                                               
                                                     
                                                                      
           
                                      
                                                  
                            
               
        
                                                                
                                                                 
                                        
         
                                                                     
               
                          
                    
                     
                                                                       
                
                                                   
                                                
                                                                         
                                                       
                                                     
              
                                        
                                                             
                                                                      
                                
                                                  
                                                                 
                                                           
                                              
                           
                       
                                                                       
                                                  
                               
                                            
                                     
                                                                           
                           
                 
             
                          
             
                                                                 
                  
               
          
              
        
                                        
                                            
                                                                      
                                                   
                                                
                                                 
                                                     
                                       
                                  
                 
              
                                          
                                         
                                                        
                                                                
                    
                                                  
                                       
                                                          
                                                                  
                 
                        
                            
                        
                                                          
                           
                                                                
             
                
                                              
                
                                                          
                                   
                  
                                                   
                                
                  
                                                
                                                     
                               
                                
                                                  
                                                
                                     
                                      
                                                          
                          
                                                          
                                                                   

                                         
                                                                 
                                                                   
              

                                                                   
                                               

                                                                
                      

                                                                      
                                                        
                                                                     
                                                                 
                                              

                                                                  
                                                       
                                                                   

                                                                    
                                                                   
                                                                     
                                                   
                                                      
                                                                  
                                                        
                                 
                                                             
                                                                          
                                                     
                                               
                                                     
                                                                      
                  
                                                                             

end MoltResearch

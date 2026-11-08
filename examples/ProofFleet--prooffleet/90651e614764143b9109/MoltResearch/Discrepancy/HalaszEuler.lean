import MoltResearch.Discrepancy.MultiplicativeC
import MoltResearch.Discrepancy.TruncatedBridge
import MoltResearch.Discrepancy.PretentiousDist
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

                                                                         
                  
                                               
                                                               
                                                                
                                                                           
                             
           
                    
                  
                  
                                    
                                                  
                                                  
               
                
          
                   
                                                                                    
                                           
                                             
                  

                                                                   
                                                  
                                                         
                                                                             
                                              
                                            
                     
                                                                         
                                                                                      
                             
                             
                                            
                                
                             
                                                                       
                                  
          
                                                                   
                                  
          
                       
                                                                      
                                                                                     
                                                          
                                                
                      
              
                                                
                                                             
              
                                                        
             

                                                                    
                                                               
                                                                    
                                     
                                                              
                                           
                                           
                                                                  
                                                   
                                       
                                                                
           
                                                      
                    
                                                                 
                          
                              
                    
                 
                                        
                   
                                          
                    
                                                  
                                                     
                                             
                                                               
                                                                                        
                           
                                                                              
                                                                              
                            
                                                                           
                                  
                          
                                                                            
                
                             
                                     
                                                            
                                                                           
                
                                    
                                                         
                              
                                        
                                             
                           
                                                                         
                                                                            
                                                  
            
                
                                                        
                      
                                                                 
                                                    
           
                                       
                              
                                                 
                     
           
               
                                                            
                                         
                     
           
                                   
              
                               
                                                                       
           
                     
                                                                      
                                                                       
                                                                          
                                                
          
              
                                                      
                                                    
           
                                 
                                                                         
                                
                                     
                                                                      
                                                                 
                                                             
                                            
                                                   
                                                                         
                         
                                  
                                                             
                                 
                                    
                                         
          
                                                                   
                       
                                  
                                                                      
                                                                      
                           
               
           
                                           
                                                  
                                                            
                                                                                
                                        
                               
                                                                     
           
                                           
                                                        
                     
                                
                                                                              
              
                                                                       
                                                                  
                                                                    
                           
                             
                                       
                     
                                                   
              
                       
                                               
                                                           
                               
                                                                      
                                                                                     
                                                                                  
             
                                                                               
                                                              
                                     
                                      
                                 
                                                        
                                                   
                  
                              
                                              
                                                 
                                           
                                   
                                                                                 
                    
             
                                    
                                                                                      
           
                         
                                                          
                                            
                                                                                      
                                                 
                                                                   
                                     
                                                                    
                                             
                              
                                                                                 
                                                                            
                                                
                                                             
                                                           
                                                                     
                                                                                       
                                               
                         
                      

                                                               
                                                           
                                                                       
                                                                      
                                                       
                                                        
                                                                            
                                  
                                    
                                                         
                                                                                  
           
                                     
                                         
                                               
                                                 
                                 
                                            
                        
                                     
               
                                                            
                                
               
        
                                               
                                                                 
                               
                                                                       
           
                     
                                                                      
                                                                       
                                                                          
                                                
          
              
                                                      
                                                            
                                                                                   
                                                               
                                            
               
                                                                      
                                                    
                                                     
                           
                                   
                                                                 
                                         
               
                                                             
                                      
                                                                                
                                     
               
                                                                 
             
                 
               
          
                            
                       
                                               
                      
                                   
                                            
                                                                       
               
                                      
                                                 
              
                                                                      
                                                                  
                                   
                                                                       
                                   
             
                                        
                                                              
               
                
                                       
                                            
                                                                
                                             
               
                          
                                                                         
                                                          
                                                 
                                                             
                                                                   
                                            
                                                   
                      
                                         
                                       
                                     
                                                      
               
                                                 
                 
                                                                   
                                                                  
                                                                          
                                                
          
                       
              
                                                  
                                                              
                                                                                 
                                   
                                 
                                                                               
                
                                                 
                                      
                        
                                                              
                                                                                   
                                                       
                                               
                                                 
                                                              
                                                     
                                                                                    
            
                                                           
                      
                                                       
                              
                                                                              
                               
                                                                         
                                                           
                                                     
                 
                                                       
                                                                                   
                                                 
                                                                     
                                                        
                                         
                                                     
                                                 
                         
                         
                            
                  
                                                            
                                                          
                                                                              
                                                            
           
               
              
                    
                                                  
                                         
              
              
                                                                                  
                                               
                                                               
                                
                                 
                                                                         
              
                                             
                                                               
                                                                        
                                                           
                                                                          
                              
                        
                                                          
                                            
                                               
                                                 
                                                                                  
           
                                                                 
                                               
                                                 
                                                                                  
           
                                                                 
                                    
                                                      
                                                     
           
                            
                                                
                                                
                                                                          
                                
                                                                                        
                                                                    
                                                
                            
                                                                        
                                                        
                              
                          
                                                                                    
                                   
                                             
                                                                         
             
                              
                               
                                                                 
                                                              
                        
                                    
                
                               
                                                        
                                                                     
                                                                            
                                                                       
                              
                     
                                 
                                              
                       
                                                                 
                            
                                                                      
                                                             
                     
             
                                        
                                                                                     
                   
               
                                          
                                                    
                             
                                                                               
                        
                                                              
                                                                  
                    
            
                                                                                       
                         
                                                                                  
            


                                                              
                                                                      
                                                     
                                                                 
                                                                     
                  
                                                
                                                                            
                                  
                                                                             
                                                                     
                      
                                                                                  
           
                                               
                                           
                                                 
                                                   
                                   
                                                    
            
                                                         
                                   
                                                                
                                                     
               
                                                             
                                                      
                                                                    
                                     
                                        
             
               
          
                                                          
                                                                       
                                     
                                        
             
               
          
                                          
           
                                                              
        
                                                                              
                                          
                                                                             
                                                    
                                              
                                               
                    
        
                                                                           
                                                
                                            
                                                      
                                                        
                                                
                                        
                                        
                                                                                
                
                                                     
                                                  
                                                
                      
              
                                                 
                                                                   
                                    
             
              
                                                      
                                              
                          
                                                                           
                                              
          
                       
                 
                                    
                                                 
                                            
                                                  
                                          
                          
             
                          
                                                                             
                                                                       
           
                                    
             
          
                                                
                                                       
                                                                   
                                                            
                                                                        
                                    
                                                               
                                                
                     
                                                                              
                                       
                                                                                  
                                               
                                                                                  
                   
                                                                                      
                           
               
                                                
                                                        
                   
              
                
                                                                                    
                   
                                                    
                                                        
                                                
                       
                                          
                          
                          
                      
                      
                                                                           
                                       
                                                                   
                       
                                                                      
            
                 
                                                                   
                     
                                                            
                                                                     
             
              
                                                
                                                         
                                                                                
                                                                                      
                          
                                                                                  
                                                    
                                                                 
                                
                                                        
                                             
                                                                                    
                                  
                                                        
                                              
                        
                                                                                 
                          
                                                                       
                        
                                                                                    
                                 


                                       
theorem prime_mem_smoothNumbers {p y : ℕ} (hp : p.Prime) (hpy : p < y) :
    p ∈ Nat.smoothNumbers y := by
  rw [Nat.mem_smoothNumbers']
  intro q hq hqp
  have := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  omega

/-- The smooth restriction of a completely multiplicative function is
completely multiplicative. -/
theorem completelyMultiplicativeC_smooth_restrict (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (y : ℕ) :
    CompletelyMultiplicativeC
      (fun n => if n ∈ Nat.smoothNumbers y then f n else 0) := by
  classical
  intro a b ha hb
  dsimp only
  by_cases hab : a * b ∈ Nat.smoothNumbers y
  · have haS : a ∈ Nat.smoothNumbers y :=
      Nat.mem_smoothNumbers_of_dvd hab ⟨b, rfl⟩
    have hbS : b ∈ Nat.smoothNumbers y :=
      Nat.mem_smoothNumbers_of_dvd hab ⟨a, mul_comm a b⟩
    rw [if_pos hab, if_pos haS, if_pos hbS, hcm a b ha hb]
  · rw [if_neg hab]
    by_cases haS : a ∈ Nat.smoothNumbers y
    · by_cases hbS : b ∈ Nat.smoothNumbers y
      · exact absurd (Nat.mul_mem_smoothNumbers haS hbS) hab
      · rw [if_neg hbS, mul_zero]
    · rw [if_neg haS, zero_mul]

                                                                    
                 
                                                                 
             
                     
                                                                 
                                     
           
                          
                                            
                                             
                                           
            
                                               

                                                                      
                                                                     
                                                                    
                                                  
                                                       
                                                      
                                                                        
                                                                  
                                                         
                                                                     
                      
                                                                
                                                                                  
           
                                                                      
               
                                                                
                          
               
              
                  
                                 
                    
                                             
                       
                 
                                 
           
               
              
         
                
          
                                                            
                         
                           
                                                     
                      
                         
                                 
                                                 
                           
                                                    
                                           
                                                                             
           
              
                                            
              
                                                           
                 
                                   
                                              
                                                          
                         
                                                   
                                                      
                                       
           
                             


                                                          
                                                                      
                                                                      
                                                                   
           
theorem smooth_tsum_eq_finprod (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (y : ℕ) (hy : 1 ≤ y) (s : ℂ) (hs : s.re = 1) :
    ∑' n : ℕ, (if n ∈ Nat.smoothNumbers y then f n else 0)
        * (if n = 0 then 0 else (n:ℂ)^(-s))
      = ∏ p ∈ y.primesBelow,
          (1 - (f p) * (p:ℂ)^(-s))⁻¹ := by
  classical
  set g : ℕ → ℂ := fun n => if n ∈ Nat.smoothNumbers y then f n else 0
    with hg_def
  have hgcm : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → g (a*b) = g a * g b := by
    intro a b ha hb
    rw [hg_def]
    exact completelyMultiplicativeC_smooth_restrict f hcm y a b ha hb
  have hg1 : g 1 = 1 := by
    rw [hg_def]
    dsimp only
    rw [if_pos (by
      rw [Nat.mem_smoothNumbers']
      intro q hq hq1
      have := Nat.le_of_dvd (by norm_num) hq1
      have := hq.two_le
      omega), h1]
  have hgb : ∀ n, ‖g n‖ ≤ 1 := by
    intro n
    rw [hg_def]
    dsimp only
    split
    · exact hb n
    · simp
  -- the monoid-hom packaging
  set F : ℕ →*₀ ℂ :=
    { toFun := fun n => g n * (if n = 0 then 0 else (n:ℂ)^(-s))
      map_zero' := by simp
      map_one' := by simp [hg1]
      map_mul' := by
        intro a b
        rcases eq_or_ne a 0 with ha | ha
        · simp [ha, hg_def]
        rcases eq_or_ne b 0 with hb0 | hb0
        · simp [hb0, hg_def]
        have hab : a * b ≠ 0 := mul_ne_zero ha hb0
        simp only [if_neg ha, if_neg hb0, if_neg hab]
        have hcast : ((a * b : ℕ) : ℂ) ^ (-s)
            = ((a : ℕ) : ℂ) ^ (-s) * ((b : ℕ) : ℂ) ^ (-s) := by
          have h1' : ((a * b : ℕ) : ℂ)
              = (((a : ℕ) : ℝ) : ℂ) * (((b : ℕ) : ℝ) : ℂ) := by
            push_cast
            ring
          have h2' : ((a : ℕ) : ℂ) = (((a : ℕ) : ℝ) : ℂ) := by
            push_cast
            ring
          have h3' : ((b : ℕ) : ℂ) = (((b : ℕ) : ℝ) : ℂ) := by
            push_cast
            ring
          rw [h1', h2', h3',
            mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
        rw [hcast, hgcm a b ha hb0]
        ring }
    with hF_def
  -- norm-summability at Re s = 1: the smooth harmonic mass converges
  have hFapply : ∀ n : ℕ, F n = g n * (if n = 0 then 0 else (n:ℂ)^(-s)) :=
    fun n => rfl
  set h : ℕ → ℝ := fun n =>
    if n ∈ Nat.smoothNumbers y then 1/(n:ℝ) else 0 with hh_def
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
  have hFle : ∀ n, ‖F n‖ ≤ h n := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · rw [hFapply, hn]
      simpa using hh_nonneg 0
    · rw [hFapply, if_neg hn, norm_mul]
      have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hnorm : ‖((n:ℕ):ℂ)^(-s)‖ = 1/(n:ℝ) := by
        rw [Complex.norm_natCast_cpow_of_pos hn0]
        rw [show (-s).re = -1 from by rw [Complex.neg_re, hs]]
        rw [Real.rpow_neg_one, one_div]
      rw [hnorm, hh_def]
      dsimp only
      rw [hg_def]
      dsimp only
      by_cases hsm : n ∈ Nat.smoothNumbers y
      · rw [if_pos hsm, if_pos hsm]
        calc ‖f n‖ * (1/(n:ℝ)) ≤ 1 * (1/(n:ℝ)) :=
            mul_le_mul_of_nonneg_right (hb n)
              (one_div_nonneg.mpr (Nat.cast_nonneg n))
          _ = 1/(n:ℝ) := one_mul _
      · rw [if_neg hsm, if_neg hsm, norm_zero, zero_mul]
  have hsum : Summable (fun n => ‖F n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hFle hh_sum
  have hEuler := EulerProduct.eulerProduct_completely_multiplicative
    (f := F) hsum
  have hzero_beyond : ∀ p : ℕ, p.Prime → y ≤ p → F p = 0 := by
    intro p hp hyp
    rw [hFapply, hg_def]
    dsimp only
    rw [if_neg (by
      intro hmem
      have := Nat.mem_smoothNumbers'.mp hmem p hp dvd_rfl
      omega), zero_mul]
  have hconst : ∀ n, y ≤ n → ∏ p ∈ Nat.primesBelow n, (1 - F p)⁻¹
      = ∏ p ∈ y.primesBelow, (1 - F p)⁻¹ := by
    intro n hn
    refine (Finset.prod_subset ?_ ?_).symm
    · intro p hp
      rw [Nat.mem_primesBelow] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p hp hnot
      rw [Nat.mem_primesBelow] at hp
      have hyp : y ≤ p := by
        by_contra hlt
        push_neg at hlt
        exact hnot (Nat.mem_primesBelow.mpr ⟨hlt, hp.2⟩)
      rw [hzero_beyond p hp.2 hyp, sub_zero, inv_one]
  have hconstT : Filter.Tendsto
      (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, (1 - F p)⁻¹)
      Filter.atTop (nhds (∏ p ∈ y.primesBelow, (1 - F p)⁻¹)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop y] with n hn
    exact (hconst n hn).symm
  have hkey := tendsto_nhds_unique hEuler hconstT
  calc ∑' n : ℕ, (if n ∈ Nat.smoothNumbers y then f n else 0)
        * (if n = 0 then 0 else (n:ℂ)^(-s))
      = ∑' n, F n := by
        refine tsum_congr fun n => ?_
        rw [hFapply, hg_def]
    _ = ∏ p ∈ y.primesBelow, (1 - F p)⁻¹ := hkey
    _ = ∏ p ∈ y.primesBelow, (1 - (f p) * (p:ℂ)^(-s))⁻¹ := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have hpp := Nat.prime_of_mem_primesBelow hp
        have hpy := (Nat.mem_primesBelow.mp hp).1
        rw [hFapply, if_neg hpp.ne_zero, hg_def]
        dsimp only
        rw [if_pos (prime_mem_smoothNumbers hpp hpy)]


set_option maxHeartbeats 1600000 in
/-- **The 1-line smooth Euler bound** (Track R, M2-i4a2): the finite
Euler product of a `1`-bounded function over the primes below `y`,
evaluated on the 1-line at frequency `ξ`, is exponentially controlled
by the prime mass minus the pretentious distance to the `ξ`-twist —
the `L^∞` input of the cheap-Halász band term, with no abscissa
shift. -/
theorem norm_smooth_finprod_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    (y : ℕ) (ξ : ℝ) :
    ‖∏ p ∈ y.primesBelow, (1 - (f p) * (p:ℂ)^(-(1 + Complex.I*(ξ:ℂ))))⁻¹‖
      ≤ Real.exp ((∑ p ∈ y.primesBelow, (1:ℝ)/p)
          - pretentiousDistSq f (fun n => (n:ℂ)^(Complex.I*(ξ:ℂ))) y + 1) := by
  classical
  set s : ℂ := 1 + Complex.I*(ξ:ℂ) with hs_def
  set w : ℕ → ℂ := fun p => f p * (p:ℂ)^(-s) with hw_def
  have hsre : s.re = 1 := by
    rw [hs_def]
    simp
  -- per-prime norm facts
  have hnw : ∀ p ∈ y.primesBelow, ‖w p‖ ≤ 1/(p:ℝ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp0 : 0 < p := hpp.pos
    rw [hw_def]
    dsimp only
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp0]
    have hre : (-s).re = -1 := by
      rw [Complex.neg_re, hsre]
    rw [hre, Real.rpow_neg_one]
    rw [one_div]
    have h1 : ‖f p‖ * ((p:ℝ))⁻¹ ≤ 1 * ((p:ℝ))⁻¹ := by
      refine mul_le_mul_of_nonneg_right (hb p) ?_
      positivity
    linarith [h1]
  have hhalf : ∀ p ∈ y.primesBelow, ‖w p‖ ≤ 1/2 := by
    intro p hp
    have hp2 := (Nat.prime_of_mem_primesBelow hp).two_le
    refine le_trans (hnw p hp) ?_
    rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < p)) (by norm_num)]
    have : (2:ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hlt1 : ∀ p ∈ y.primesBelow, ‖w p‖ < 1 := by
    intro p hp
    have := hhalf p hp
    linarith
  -- per-factor exponential bound
  have hfac : ∀ p ∈ y.primesBelow,
      ‖(1 - w p)⁻¹‖ ≤ Real.exp ((w p).re + ‖w p‖^2) := by
    intro p hp
    have hne : (1 : ℂ) - w p ≠ 0 := by
      intro h
      have h1 : ‖(1:ℂ)‖ = ‖w p‖ := by
        rw [show (1:ℂ) = w p from by linear_combination h]
      rw [norm_one] at h1
      have := hlt1 p hp
      linarith
    have hpos : 0 < ‖(1 - w p)⁻¹‖ := by
      rw [norm_inv]
      have : 0 < ‖(1:ℂ) - w p‖ := norm_pos_iff.mpr hne
      positivity
    rw [← Real.exp_log hpos, Real.exp_le_exp]
    have hlogre : Real.log ‖(1 - w p)⁻¹‖
        = (Complex.log ((1 - w p)⁻¹)).re := by
      rw [Complex.log_re]
    rw [hlogre]
    have hbound := Complex.norm_log_one_sub_inv_sub_self_le (hlt1 p hp)
    have hre_diff : (Complex.log ((1 - w p)⁻¹)).re - (w p).re
        ≤ ‖Complex.log ((1 - w p)⁻¹) - w p‖ := by
      calc (Complex.log ((1 - w p)⁻¹)).re - (w p).re
          = (Complex.log ((1 - w p)⁻¹) - w p).re := by
            rw [Complex.sub_re]
        _ ≤ ‖Complex.log ((1 - w p)⁻¹) - w p‖ := Complex.re_le_norm _
    have hinv2 : (1 - ‖w p‖)⁻¹ ≤ 2 := by
      have := hhalf p hp
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hsq : ‖w p‖^2 * (1 - ‖w p‖)⁻¹ / 2 ≤ ‖w p‖^2 := by
      have h0 : (0:ℝ) ≤ ‖w p‖^2 := sq_nonneg _
      nlinarith
    linarith [hbound, hre_diff, hsq]
  -- assemble the product
  calc ‖∏ p ∈ y.primesBelow, (1 - w p)⁻¹‖
      = ∏ p ∈ y.primesBelow, ‖(1 - w p)⁻¹‖ := norm_prod _ _
    _ ≤ ∏ p ∈ y.primesBelow, Real.exp ((w p).re + ‖w p‖^2) := by
        refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) hfac
    _ = Real.exp (∑ p ∈ y.primesBelow, ((w p).re + ‖w p‖^2)) := by
        rw [Real.exp_sum]
    _ ≤ Real.exp ((∑ p ∈ y.primesBelow, (1:ℝ)/p)
          - pretentiousDistSq f (fun n => (n:ℂ)^(Complex.I*(ξ:ℂ))) y + 1) := by
        rw [Real.exp_le_exp]
        have hsum_re : ∑ p ∈ y.primesBelow, (w p).re
            = (∑ p ∈ y.primesBelow, (1:ℝ)/p)
              - pretentiousDistSq f (fun n => (n:ℂ)^(Complex.I*(ξ:ℂ))) y := by
          unfold pretentiousDistSq
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpp := Nat.prime_of_mem_primesBelow hp
          have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
          have hsplit : w p = (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))) / (p:ℂ) := by
            rw [hw_def]
            dsimp only
            rw [hs_def]
            rw [show -(1 + Complex.I*(ξ:ℂ))
                = (-(Complex.I*(ξ:ℂ))) + (-1) from by ring]
            rw [Complex.cpow_add _ _ (by
              exact_mod_cast hpp.ne_zero : ((p:ℕ):ℂ) ≠ 0)]
            rw [Complex.cpow_neg_one]
            field_simp
          rw [hsplit]
          have hdiv_re : ((f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))) / (p:ℂ)).re
              = (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))).re / (p:ℝ) := by
            have h1 : (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))) / (p:ℂ)
                = (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ))))
                  * (((1/(p:ℝ)):ℝ):ℂ) := by
              push_cast
              field_simp
            rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              mul_zero, sub_zero, mul_one_div]
          rw [hdiv_re]
          have hconjp : (starRingEnd ℂ) (((p:ℕ):ℂ)^(Complex.I*(ξ:ℂ)))
              = ((p:ℕ):ℂ)^(-(Complex.I*(ξ:ℂ))) := by
            have hplus : ((p:ℕ):ℂ) ^ (Complex.I * (ξ:ℂ))
                = Complex.exp (((ξ * Real.log p : ℝ) : ℂ) * Complex.I) := by
              rw [Complex.cpow_def_of_ne_zero
                (by exact_mod_cast hpp.ne_zero)]
              congr 1
              push_cast
              ring
            have hminus : ((p:ℕ):ℂ) ^ (-(Complex.I * (ξ:ℂ)))
                = Complex.exp (-(((ξ * Real.log p : ℝ) : ℂ) * Complex.I)) := by
              rw [Complex.cpow_def_of_ne_zero
                (by exact_mod_cast hpp.ne_zero)]
              congr 1
              push_cast
              ring
            rw [hplus, hminus, ← Complex.exp_conj, map_mul,
              Complex.conj_ofReal, Complex.conj_I]
            ring_nf
          dsimp only
          rw [hconjp]
          ring
        have hsum_sq : ∑ p ∈ y.primesBelow, ‖w p‖^2 ≤ 1 := by
          have h1 : ∑ p ∈ y.primesBelow, ‖w p‖^2
              ≤ ∑ p ∈ y.primesBelow, (1/(p:ℝ))^2 := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hle := hnw p hp
            have h0 : (0:ℝ) ≤ ‖w p‖ := norm_nonneg _
            nlinarith
          have h2 : ∑ p ∈ y.primesBelow, (1/(p:ℝ))^2
              ≤ ∑ p ∈ y.primesBelow, 1/((p:ℝ)*((p:ℝ)-1)) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp2 : (2:ℝ) ≤ p := by
              exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
            rw [div_pow, one_pow]
            rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
            nlinarith
          linarith [h1, h2, sum_one_div_mul_pred_primesBelow_le y]
        rw [Finset.sum_add_distrib, hsum_re]
        linarith [hsum_sq]


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


set_option maxHeartbeats 1600000 in
/-- **The band sup for the smooth polynomial** (Track R, M2-i4c1a):
on any frequency `ξ`, the `y₂`-smooth phase polynomial truncated at
`x` is bounded by the 1-line Euler product bound — the prime mass
minus the pretentious distance floor `M` at scale `x`, corrected by
twice the mass difference (the truncation transfer) — plus the
Rankin-`δ` polynomial-versus-series tail. This is the `Bband` input
of the band/tail Hölder split, with every constant explicit. -/
theorem norm_smooth_poly_band_le (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (y₂ x : ℕ) (hy₂ : 1 ≤ y₂) (hyx : y₂ ≤ x)
    (hx : 1 ≤ x) (ξ M δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : M ≤ pretentiousDistSq f
      (fun n => (n:ℂ)^(Complex.I*((2*Real.pi*ξ : ℝ):ℂ))) x) :
    ‖∑ n ∈ (Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂),
        (f n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖
      ≤ Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
            + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
              - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
        + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
  classical
  set c : ℝ := 2*Real.pi*ξ with hc_def
  set s : ℂ := 1 + Complex.I*((c:ℝ):ℂ) with hs_def
  have hsre : s.re = 1 := by
    rw [hs_def]
    simp
  -- the polynomial index set is the smooth-numbers-up-to Finset
  have hconv : (Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂)
      = Nat.smoothNumbersUpTo x y₂ := by
    ext n
    rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩
      exact ⟨⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers h3),
        h2⟩, h3⟩
  -- each term is the L-series term at s = 1 + 2πiξ
  have hterm : ∀ n ∈ Nat.smoothNumbersUpTo x y₂,
      (f n/(n:ℂ)) * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)
        = (if n ∈ Nat.smoothNumbers y₂ then f n else 0)
            * (if n = 0 then 0 else (n:ℂ)^(-s)) := by
    intro n hn
    rw [Nat.mem_smoothNumbersUpTo] at hn
    have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hn.2
    have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    rw [if_pos hn.2, if_neg hn0]
    have hn0' : (n:ℂ) ≠ 0 := by exact_mod_cast hn0
    have hlogn : Complex.log (n:ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [show ((n:ℕ):ℂ) = (((n:ℕ):ℝ):ℂ) from by norm_cast]
      exact (Complex.ofReal_log hnpos.le).symm
    have hcpow : (n:ℂ)^(-s)
        = ((1:ℂ)/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ) := by
      rw [Complex.cpow_def_of_ne_zero hn0', hlogn,
        Real.fourierChar_apply]
      rw [show ((Real.log n : ℝ) : ℂ) * (-s)
          = ((-(Real.log n) : ℝ) : ℂ)
            + ((2*Real.pi*(-(Real.log n * ξ)) : ℝ) : ℂ) * Complex.I from by
        rw [hs_def, hc_def]
        push_cast
        ring]
      rw [Complex.exp_add]
      congr 1
      rw [← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hnpos]
      rw [one_div]
      push_cast
      ring
    rw [hcpow]
    ring
  rw [hconv, Finset.sum_congr rfl hterm]
  -- triangle against the full smooth series
  set T : ℂ := ∑' n : ℕ, (if n ∈ Nat.smoothNumbers y₂ then f n else 0)
    * (if n = 0 then 0 else (n:ℂ)^(-s)) with hT_def
  set A : ℂ := ∑ n ∈ Nat.smoothNumbersUpTo x y₂,
    (if n ∈ Nat.smoothNumbers y₂ then f n else 0)
      * (if n = 0 then 0 else (n:ℂ)^(-s)) with hA_def
  have htri : ‖A‖ ≤ ‖T‖ + ‖T - A‖ := by
    calc ‖A‖ = ‖T - (T - A)‖ := by
          congr 1
          ring
      _ ≤ ‖T‖ + ‖T - A‖ := norm_sub_le _ _
  refine le_trans htri (add_le_add ?_ ?_)
  · -- the head: Euler product bound + distance transfer
    have heq := smooth_tsum_eq_finprod f hcm h1 hb y₂ hy₂ s hsre
    rw [hT_def, heq]
    have hprod := norm_smooth_finprod_le f hb y₂ c
    have hshape : ∏ p ∈ y₂.primesBelow,
        (1 - (f p) * (p:ℂ)^(-(1 + Complex.I*((c:ℝ):ℂ))))⁻¹
          = ∏ p ∈ y₂.primesBelow, (1 - (f p) * (p:ℂ)^(-s))⁻¹ := by
      rw [hs_def]
    rw [hshape] at hprod
    refine le_trans hprod ?_
    rw [Real.exp_le_exp]
    -- the truncation transfer on the pretentious distance
    have htwist_norm : ∀ p,
        ‖(fun n : ℕ => (n:ℂ)^(Complex.I*((c:ℝ):ℂ))) p‖ ≤ 1 := by
      intro p
      dsimp only
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp
        rcases eq_or_ne (Complex.I*((c:ℝ):ℂ)) 0 with h | h
        · rw [h, Complex.cpow_zero]
          norm_num
        · rw [show ((0:ℕ):ℂ) = 0 from by norm_cast,
            Complex.zero_cpow h]
          norm_num
      · rw [Complex.norm_natCast_cpow_of_pos hp]
        have hre : (Complex.I*((c:ℝ):ℂ)).re = 0 := by
          simp [Complex.mul_re]
        rw [hre, Real.rpow_zero]
    have htrans := pretentiousDistSq_le_add_mass f
      (fun n : ℕ => (n:ℂ)^(Complex.I*((c:ℝ):ℂ)))
      (fun p => hb p) htwist_norm hyx
    have hMc : M ≤ pretentiousDistSq f
        (fun n : ℕ => (n:ℂ)^(Complex.I*((c:ℝ):ℂ))) x := hM
    linarith [htrans, hMc]
  · -- the tail: the Rankin-δ polynomial-versus-series gap
    exact norm_smooth_tsum_sub_sum_le f hb y₂ x hx s hsre δ hδ0 hδ1

                                         
                                                                 
                                                                   
              

                                                                   
                                               

                                                                
                      

                                                                      
                                                        
                                                                     
                                                                 
                                              

                                                                  
                                                       
                                                                   

                                                                    
                                                                   
                                                                     
                                                   
                                                      
                                                                  
                                                        
                                 
                                                             
                                                                          
                                                     
                                               
                                                     
                                                                      
                  
                                                                             

end MoltResearch

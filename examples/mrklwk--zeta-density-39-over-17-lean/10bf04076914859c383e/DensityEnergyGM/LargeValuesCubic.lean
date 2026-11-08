module
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import DensityEnergyGM.LargeValuesLanguage
public import GuthMaynard.NativeSource.GuthMaynard.LargeValuesReflection
public import GuthMaynard.NativeSource.GuthMaynard.Separated

@[expose] public section

open Complex Finset Filter MeasureTheory Real Set
open scoped BigOperators

namespace GuthMaynard.NativeMoment

/-!
# Cubic Poisson trace and the `S₁/S₂/S₃` split

This module formalizes Guth--Maynard Lemma 4.5 and the decomposition (5.5).
Every dual sum is an absolutely summable integer series.  The three pieces are
obtained by writing each Gram kernel as its zero Fourier mode plus its complete
nonzero-frequency tail and expanding the resulting cubic product.
-/

/-- The scaled `m`-th Fourier mode `N h-hat_t(Nm)` in the source Poisson
formula. -/
noncomputable def gmScaledTraceMode (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) (m : ℤ) : ℂ :=
  (N : ℂ) * gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))

/-- The complete nonzero-frequency tail at ordinate difference `t`. -/
noncomputable def gmTraceNonzeroTailAt (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) : ℂ :=
  ∑' m : ℤ, if m = 0 then 0 else gmScaledTraceMode cutoff N t m

/-- The scaled zero Fourier mode. -/
noncomputable def gmTraceZeroMode (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) : ℂ :=
  gmScaledTraceMode cutoff N t 0

                                                                    
                          
                                                 
                          
             
                                                                         

                                                                  
                                  
                                              
                                                                        
                                                                        
                                              

                                                                           
                                                                             
                 
theorem gmTraceNonzeroTailAt_bound (cutoff : GMSmoothCutoff)
    (q : ℕ) (hq : 2 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 0 < N → ∀ t : ℝ,
      ‖gmTraceNonzeroTailAt cutoff N t‖ ≤
        K * (1 + |t|) ^ q / (N : ℝ) ^ (q - 1) := by
  obtain ⟨C, hC, hDecay⟩ := gmTraceFourier_uniform_decay cutoff q
  have hSeries : Summable (fun m : ℤ ↦ ‖1 / (m : ℂ) ^ q‖) := by
    have hNorm : (fun m : ℤ ↦ ‖1 / (m : ℂ) ^ q‖) =
        fun m : ℤ ↦ |1 / (m : ℝ) ^ q| := by
      funext m
      simp only [norm_div, norm_one, norm_pow, Complex.norm_intCast,
        abs_div, abs_one, pow_abs]
    rw [hNorm, summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (by omega)
  let B : ℝ := ∑' m : ℤ, ‖1 / (m : ℂ) ^ q‖
  have hB : 0 ≤ B := tsum_nonneg fun m ↦ norm_nonneg _
  refine ⟨C * B + 1, by positivity, ?_⟩
  intro N hN t
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let scale : ℝ := C * (1 + |t|) ^ q / (N : ℝ) ^ (q - 1)
  have hPointwise : ∀ m : ℤ,
      ‖if m = 0 then 0 else gmScaledTraceMode cutoff N t m‖ ≤
        scale * ‖1 / (m : ℂ) ^ q‖ := by
    intro m
    by_cases hm : m = 0
    · have hq0 : q ≠ 0 := by omega
      simp [hm, hq0]
    · have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have hmAbs : 0 < |(m : ℝ)| := abs_pos.mpr hmReal
      have hFreqAbs : |(N : ℝ) * (m : ℝ)| =
          (N : ℝ) * |(m : ℝ)| := by
        rw [abs_mul, abs_of_pos hNr]
      have hFreqPos : 0 < |(N : ℝ) * (m : ℝ)| := by positivity
      have hFourier :
          ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
            C * (1 + |t|) ^ q /
              |(N : ℝ) * (m : ℝ)| ^ q := by
        rw [le_div_iff₀ (pow_pos hFreqPos q)]
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          hDecay t ((N : ℝ) * (m : ℝ))
      simp only [ite_false, hm, gmScaledTraceMode, norm_mul,
        Complex.norm_natCast, norm_div, norm_one, norm_pow,
        Complex.norm_intCast]
      calc
        (N : ℝ) * ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
            (N : ℝ) *
              (C * (1 + |t|) ^ q /
                |(N : ℝ) * (m : ℝ)| ^ q) := by gcongr
        _ = scale * (1 / |(m : ℝ)| ^ q) := by
          rw [hFreqAbs, mul_pow]
          have hqEq : q = (q - 1) + 1 := by omega
          have hNpow : (N : ℝ) ^ q =
              (N : ℝ) ^ (q - 1) * (N : ℝ) := by
            conv_lhs => rw [hqEq, pow_succ]
          dsimp only [scale]
          rw [hNpow]
          field_simp
  have hScaled : Summable (fun m : ℤ ↦ scale * ‖1 / (m : ℂ) ^ q‖) :=
    hSeries.mul_left scale
  have hBound := tsum_of_norm_bounded hScaled.hasSum hPointwise
  rw [tsum_mul_left] at hBound
  change ‖gmTraceNonzeroTailAt cutoff N t‖ ≤ scale * B at hBound
  calc
    ‖gmTraceNonzeroTailAt cutoff N t‖ ≤ scale * B := hBound
    _ ≤ (C * B + 1) * (1 + |t|) ^ q / (N : ℝ) ^ (q - 1) := by
      dsimp only [scale]
      have hPow : 0 < (N : ℝ) ^ (q - 1) := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hPow).2
      have htPow : 0 ≤ (1 + |t|) ^ q := by positivity
      nlinarith

/-- A uniform bound for every scaled zero mode. -/
theorem gmTraceZeroMode_bound (cutoff : GMSmoothCutoff) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (t : ℝ),
      ‖gmTraceZeroMode cutoff N t‖ ≤ (N : ℝ) * B := by
  obtain ⟨C, hC, hDecay⟩ := gmTraceFourier_uniform_decay cutoff 0
  refine ⟨C + 1, by positivity, ?_⟩
  intro N t
  have h := hDecay t 0
  simp only [abs_zero, pow_zero, one_mul] at h
  simp only [gmTraceZeroMode, gmScaledTraceMode, Int.cast_zero, mul_zero,
    norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (h.trans (by nlinarith [hC]))
    (Nat.cast_nonneg N)

/-- A separated nonzero ordinate difference makes its scaled zero mode
arbitrarily small. -/
theorem gmTraceZeroMode_separated_bound (cutoff : GMSmoothCutoff)
    (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) {δ t : ℝ}, 0 < δ → δ ≤ |t| →
      ‖gmTraceZeroMode cutoff N t‖ ≤
        (N : ℝ) * C / δ ^ q := by
  obtain ⟨C, hC, hDecay⟩ := gmTraceFourier_zero_uniform_decay_source cutoff q
  refine ⟨C, hC, ?_⟩
  intro N δ t hδ ht
  have htPos : 0 < |t| := hδ.trans_le ht
  have hFourier : ‖gmTraceFourier cutoff t 0‖ ≤ C / |t| ^ q := by
    rw [le_div_iff₀ (pow_pos htPos q)]
    simpa [mul_comm] using hDecay t
  simp only [gmTraceZeroMode, gmScaledTraceMode, Int.cast_zero, mul_zero,
    norm_mul, Complex.norm_natCast]
  calc
    (N : ℝ) * ‖gmTraceFourier cutoff t 0‖ ≤
        (N : ℝ) * (C / |t| ^ q) := by gcongr
    _ = (N : ℝ) * C / |t| ^ q := by ring
    _ ≤ (N : ℝ) * C / δ ^ q := by
      have hpow : δ ^ q ≤ |t| ^ q := pow_le_pow_left₀ hδ.le ht q
      exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg N) hC.le)
        (pow_pos hδ q) hpow

                                             
                                                                 
             
                                    
                                 
                               
                                                  
                                                
                                                
                                                  
              
                                                             
                                                     
                                            
        
                                              
                                                                                
                                                                
            
                                         
                                                                     
                                                      
                      
                                                                          
                                     
             
                                                          
                                                          
             
        
           
        

                                                                            
                                         
                                                                  
                                  
                                                    
                                                                  
                                                                             
                                                       
                                                                     
        
                                                                   
               
                
                                                                 
                          
                  
                                            
                                                          
         
                                              
               
              
                                       
                              
                             
                                          
                         
                                                      
                       
                                
                
                                                                
                                                                          
                                        
                                                 
              
                            
            
     

                                                                           
                                                     
                                                  
                                    
                                                                     
                                                       
                                                                        
                                       
                
                        
                                          
                                                              
                                                         
                           
                                                                        
                       
                              
              
                                  
                                                               
                                  
           
                                                     
           
                         
                                      
                                              
                                
                                                              
                                                              
                           
         

                                                        
                 
                                       
                                           
                                                     
                                                     
                                                               
                                           
           
      

                                                        
                                                                   
                         
                                              
                                                  
                                                    
                                                    

                                                         
                                                                       
                         
                                                            

                                                          
                                                                        
                         
                                              
                                
                                                    
                                                      
                                                      

       
                                                                
                                
                                               
                                           
                                           

                                                                         
                                        
                                                                       
                            
                                
                                                                            
                                                                 
              
                                                                  
                                                    
                               
                                                          
                                                            
                                                            
                      
        
        
                                                   
                               
                                                          
                                                            
                                                            
                   
                         
                                                           
                                  
                  
                                   
                                     
                
                
                          
                                           
                      
                
                        
                                         
                    
              
                                      
                                             
                                                                        
                       
            
            
                               
                            
            
                               
                            
            
                               
                            
            
                      
           
                        
             
          
                
              

                                                            
noncomputable def gmCubicS1Summand (cutoff : GMSmoothCutoff) (N : ℕ)
    {W : Finset ℝ} (t u v : GMRow W) : ℂ :=
  (gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
    gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
    gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ)))

/-- The piece with exactly one nonzero Fourier frequency. -/
noncomputable def gmCubicS1 (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    gmCubicS1Summand cutoff N t u v

                                                     
                                                                         
                                           
                                                     
                                                       
                                                  

                                                      
                                                                          
                                           
                                                     
                                                  
                                                       

                                                     
                                                                         
                                           
                                                
                                                       
                                                       

                                                                     
                                                                    
                                           
                                        
                                           
                                          

                                                              
                                                             
                         
                                              
                                   

                                                            
                                                             
                         
                                              
                                                       
                                                         
                                                         

                                                                          
                     
                                                                     
                                         
                
                                                                           
                                                  
                                                       
                                                                
                                                         
                                                                
                                                         
                                                                    
                               
                            
            
                            
            
                            
            
                                                                       
                                                 
      
                                                     
                                                         
                                                                
                                                          
                                                         
                                                                 
                                                          
                                                         
                                                                 
                                                        
                                                         
                                                          
                                                        
                                                                
                                                         
                                                                
                                                         
                                                                          
                                                         

                                                                          
                                                                        
                                                            
                                         
                
                                                                           
                                                         
                                                         
                                                        
                                                             
                                                                 
                                   
                                    
                            
            
                            
            
                            
            
      

private theorem gmRow_difference_abs_le {T : ℝ} {W : Finset ℝ}
    (hW : InBaseInterval T W) (t u : GMRow W) :
    |(t : ℝ) - (u : ℝ)| ≤ T := by
  have ht := hW t t.property
  have hu := hW u u.property
  rw [Set.mem_Icc] at ht hu
  rw [abs_le]
  constructor <;> linarith

private theorem gmRow_difference_separated {δ : ℝ} {W : Finset ℝ}
    (hSep : IsSeparated δ W) (t u : GMRow W) (htu : t ≠ u) :
    δ ≤ |(t : ℝ) - (u : ℝ)| := by
  have hval : (t : ℝ) ≠ (u : ℝ) := fun h => htu (Subtype.ext h)
  simpa [Real.dist_eq] using hSep t t.property u u.property hval

                                                                       
                                                                            
       
                                                             
                                                                     
                              
                                                       
                                          
                                                      
                     
                                           
                                                      
              
                                           
                               
                         
                                                           
                             
                                                
        
                                                     
                                                                
                                                       
                                                   
                                    
                                                                
           
                                                          
                                 
                                                                  
                           
              
                                                       
                                
      
                                                                      
                       
                            

                                                                          
                                                                             
                                          
theorem gmCubicS1_quantitative (cutoff : GMSmoothCutoff) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ) {T δ : ℝ},
      0 < N → 0 < δ → IsSeparated δ W → InBaseInterval T W →
      ‖gmCubicS1 cutoff N W‖ ≤
        K * (W.card : ℝ) ^ 3 *
          ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
            (N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by
  obtain ⟨B, hB, hZero⟩ := gmTraceZeroMode_bound cutoff
  obtain ⟨C, hC, hSmall⟩ := gmTraceZeroMode_separated_bound cutoff q
  obtain ⟨L, hL, hTail⟩ := gmTraceNonzeroTailAt_bound cutoff 2 (by norm_num)
  obtain ⟨D, hD, hTailZero⟩ :=
    gmTraceNonzeroTailAt_bound cutoff 30 (by norm_num)
  let K : ℝ := 3 * (L * B * C + B ^ 2 * D) + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro N W T δ hN hδ hSep hW
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let offMajor : ℝ :=
    L * (1 + |T|) ^ 2 / (N : ℝ) *
      ((N : ℝ) * B) * ((N : ℝ) * C / δ ^ q)
  let diagMajor : ℝ :=
    3 * ((N : ℝ) * B) ^ 2 *
      (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29)
  have hOffNonneg : 0 ≤ offMajor := by dsimp only [offMajor]; positivity
  have hDiagNonneg : 0 ≤ diagMajor := by dsimp only [diagMajor]; positivity
  have hTailAny : ∀ t u : GMRow W,
      ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ≤
        L * (1 + |T|) ^ 2 / (N : ℝ) := by
    intro t u
    have hdiff := gmRow_difference_abs_le hW t u
    have hbase : 1 + |(t : ℝ) - (u : ℝ)| ≤ 1 + |T| := by
      have hT0 : 0 ≤ T := by
        have ht := hW t t.property
        rw [Set.mem_Icc] at ht
        linarith
      rw [abs_of_nonneg hT0]
      linarith
    calc
      ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ≤
          L * (1 + |(t : ℝ) - (u : ℝ)|) ^ 2 /
            (N : ℝ) ^ (2 - 1) := hTail N hN ((t : ℝ) - (u : ℝ))
      _ ≤ L * (1 + |T|) ^ 2 / (N : ℝ) := by
        simp only [Nat.reduceSubDiff, pow_one]
        gcongr
  have hTailDiag : ‖gmTraceNonzeroTailAt cutoff N 0‖ ≤
      D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29 := by
    simpa using hTailZero N hN 0
  have hSummand : ∀ t u v : GMRow W,
      ‖gmCubicS1Summand cutoff N t u v‖ ≤ offMajor * 3 + diagMajor := by
    intro t u v
    by_cases hAll : t = u ∧ u = v
    · rcases hAll with ⟨rfl, rfl⟩
      simp only [sub_self, gmCubicS1Summand]
      have hDiagOne :
          ‖gmTraceNonzeroTailAt cutoff N 0‖ *
              ‖gmTraceZeroMode cutoff N 0‖ *
                ‖gmTraceZeroMode cutoff N 0‖ ≤
            ((N : ℝ) * B) ^ 2 *
              (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
        calc
          ‖gmTraceNonzeroTailAt cutoff N 0‖ *
              ‖gmTraceZeroMode cutoff N 0‖ *
                ‖gmTraceZeroMode cutoff N 0‖ ≤
            (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) *
              ((N : ℝ) * B) * ((N : ℝ) * B) := by
                gcongr
                · exact hZero N 0
                · exact hZero N 0
              
          _ = _ := by ring
      calc
        ‖gmTraceNonzeroTailAt cutoff N 0 * gmTraceZeroMode cutoff N 0 *
              gmTraceZeroMode cutoff N 0 +
            gmTraceZeroMode cutoff N 0 * gmTraceNonzeroTailAt cutoff N 0 *
              gmTraceZeroMode cutoff N 0 +
            gmTraceZeroMode cutoff N 0 * gmTraceZeroMode cutoff N 0 *
              gmTraceNonzeroTailAt cutoff N 0‖ ≤
            3 * ((N : ℝ) * B) ^ 2 *
              (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
          calc
            ‖gmTraceNonzeroTailAt cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceZeroMode cutoff N 0 +
                gmTraceZeroMode cutoff N 0 * gmTraceNonzeroTailAt cutoff N 0 *
                  gmTraceZeroMode cutoff N 0 +
                gmTraceZeroMode cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceNonzeroTailAt cutoff N 0‖ ≤
              ‖gmTraceNonzeroTailAt cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceZeroMode cutoff N 0‖ +
                ‖gmTraceZeroMode cutoff N 0 * gmTraceNonzeroTailAt cutoff N 0 *
                  gmTraceZeroMode cutoff N 0‖ +
                ‖gmTraceZeroMode cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceNonzeroTailAt cutoff N 0‖ := by
                    calc
                      ‖(_ + _) + _‖ ≤ ‖_ + _‖ + ‖_‖ := norm_add_le _ _
                      _ ≤ (‖_‖ + ‖_‖) + ‖_‖ := by
                        gcongr
                        exact norm_add_le _ _
            _ ≤ 3 * ((N : ℝ) * B) ^ 2 *
                (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                  simp only [norm_mul]
                  have hDiagTwo :
                      ‖gmTraceZeroMode cutoff N 0‖ *
                          ‖gmTraceNonzeroTailAt cutoff N 0‖ *
                            ‖gmTraceZeroMode cutoff N 0‖ ≤
                        ((N : ℝ) * B) ^ 2 *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                    calc
                      _ ≤ ((N : ℝ) * B) *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) *
                            ((N : ℝ) * B) := by
                              gcongr
                              · exact hZero N 0
                              · exact hZero N 0
                      _ = _ := by ring
                  have hDiagThree :
                      ‖gmTraceZeroMode cutoff N 0‖ *
                          ‖gmTraceZeroMode cutoff N 0‖ *
                            ‖gmTraceNonzeroTailAt cutoff N 0‖ ≤
                        ((N : ℝ) * B) ^ 2 *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                    calc
                      _ ≤ ((N : ℝ) * B) * ((N : ℝ) * B) *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                            gcongr
                            · exact hZero N 0
                            · exact hZero N 0
                      _ = _ := by ring
                  nlinarith
      _ = diagMajor := by rfl
      _ ≤ offMajor * 3 + diagMajor := by nlinarith
    · have hTerm1 :
          ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤ offMajor := by
        have hCases : u ≠ v ∨ v ≠ t := by
          by_cases huv : u = v
          · right
            intro hvt
            apply hAll
            subst v
            subst u
            exact ⟨rfl, rfl⟩
          · exact Or.inl huv
        rcases hCases with huv | hvt
        · simp only [norm_mul]
          calc
            ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              (L * (1 + |T|) ^ 2 / (N : ℝ)) *
                ((N : ℝ) * C / δ ^ q) * ((N : ℝ) * B) := by
                  gcongr
                  · exact hTailAny t u
                  · exact hSmall N hδ (gmRow_difference_separated hSep u v huv)
                  · exact hZero N ((v : ℝ) - (t : ℝ))
            _ = offMajor := by dsimp only [offMajor]; ring
        · simp only [norm_mul]
          calc
            ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              (L * (1 + |T|) ^ 2 / (N : ℝ)) *
                ((N : ℝ) * B) * ((N : ℝ) * C / δ ^ q) := by
                  gcongr
                  · exact hTailAny t u
                  · exact hZero N ((u : ℝ) - (v : ℝ))
                  · exact hSmall N hδ (gmRow_difference_separated hSep v t hvt)
            _ = offMajor := by rfl
      have hTerm2 :
          ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤ offMajor := by
        have hCases : t ≠ u ∨ v ≠ t := by
          by_cases htu : t = u
          · right
            intro hvt
            apply hAll
            subst u
            subst v
            exact ⟨rfl, rfl⟩
          · exact Or.inl htu
        rcases hCases with htu | hvt
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * C / δ ^ q) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) * ((N : ℝ) * B) := by
                  gcongr
                  · exact hSmall N hδ (gmRow_difference_separated hSep t u htu)
                  · exact hTailAny u v
                  · exact hZero N ((v : ℝ) - (t : ℝ))
            _ = offMajor := by dsimp only [offMajor]; ring
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * B) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) *
                  ((N : ℝ) * C / δ ^ q) := by
                    gcongr
                    · exact hZero N ((t : ℝ) - (u : ℝ))
                    · exact hTailAny u v
                    · exact hSmall N hδ (gmRow_difference_separated hSep v t hvt)
            _ = offMajor := by dsimp only [offMajor]; ring
      have hTerm3 :
          ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤ offMajor := by
        have hCases : t ≠ u ∨ u ≠ v := by
          by_cases htu : t = u
          · right
            intro huv
            exact hAll ⟨htu, huv⟩
          · exact Or.inl htu
        rcases hCases with htu | huv
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * C / δ ^ q) * ((N : ℝ) * B) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) := by
                  gcongr
                  · exact hSmall N hδ (gmRow_difference_separated hSep t u htu)
                  · exact hZero N ((u : ℝ) - (v : ℝ))
                  · exact hTailAny v t
            _ = offMajor := by dsimp only [offMajor]; ring
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * B) * ((N : ℝ) * C / δ ^ q) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) := by
                  gcongr
                  · exact hZero N ((t : ℝ) - (u : ℝ))
                  · exact hSmall N hδ (gmRow_difference_separated hSep u v huv)
                  · exact hTailAny v t
            _ = offMajor := by dsimp only [offMajor]; ring
      unfold gmCubicS1Summand
      calc
        ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
            gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
            gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
            ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ +
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ +
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ := by
                  exact (norm_add_le _ _).trans
                    (by gcongr; exact norm_add_le _ _)
        _ ≤ offMajor * 3 := by nlinarith
        _ ≤ offMajor * 3 + diagMajor := le_add_of_nonneg_right hDiagNonneg
  unfold gmCubicS1
  calc
    ‖∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmCubicS1Summand cutoff N t u v‖ ≤
        ∑ t : GMRow W, ‖∑ u : GMRow W, ∑ v : GMRow W,
          gmCubicS1Summand cutoff N t u v‖ := norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W,
        ‖∑ v : GMRow W, gmCubicS1Summand cutoff N t u v‖ := by
          apply Finset.sum_le_sum
          intro t ht
          exact norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        ‖gmCubicS1Summand cutoff N t u v‖ := by
          apply Finset.sum_le_sum
          intro t ht
          apply Finset.sum_le_sum
          intro u hu
          exact norm_sum_le _ _
    _ ≤ ∑ _t : GMRow W, ∑ _u : GMRow W, ∑ _v : GMRow W,
        (offMajor * 3 + diagMajor) := by
          gcongr with t ht u hu v hv
          exact hSummand t u v
    _ = (W.card : ℝ) ^ 3 * (offMajor * 3 + diagMajor) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring
    _ ≤ K * (W.card : ℝ) ^ 3 *
          ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
            (N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by
      dsimp only [offMajor, diagMajor, K]
      have hFirst :
          L * (1 + |T|) ^ 2 / (N : ℝ) * ((N : ℝ) * B) *
              ((N : ℝ) * C / δ ^ q) =
            L * B * C * ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q) := by
        field_simp [hNr.ne']
      have hSecond :
          3 * ((N : ℝ) * B) ^ 2 *
              (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) =
            3 * B ^ 2 * D * ((N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by
        norm_num
        ring
      rw [hFirst, hSecond]
      have hCardNonneg : 0 ≤ (W.card : ℝ) ^ 3 := by positivity
      have hx : 0 ≤ (N : ℝ) * (1 + |T|) ^ 2 / δ ^ q := by positivity
      have hy : 0 ≤ (N : ℝ) ^ 2 / (N : ℝ) ^ 29 := by positivity
      calc
        (W.card : ℝ) ^ 3 *
              (L * B * C * ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q) * 3 +
                3 * B ^ 2 * D * ((N : ℝ) ^ 2 / (N : ℝ) ^ 29)) ≤
            (W.card : ℝ) ^ 3 *
              (K * ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
                (N : ℝ) ^ 2 / (N : ℝ) ^ 29)) := by
          apply mul_le_mul_of_nonneg_left _ hCardNonneg
          nlinarith [mul_nonneg (mul_nonneg hL.le hB.le) hC.le,
            mul_nonneg (sq_nonneg B) hD.le]
        _ = K * (W.card : ℝ) ^ 3 *
              ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
                (N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by ring

                                                                       
                                                                         
                                                                     
                                                                   
                                                                              
                                                        
                                                 
                                                
                                            
                                               
                                                             
                                     
                                                    
                                                     
                                      
                       
                            
                    
                                            
                                                           
                                               
              
                                          
                                      
                                                
                                                
                                                     
        
                                       
                                                
                              
                                          
                                                       
              
                                               
        
                                                
                                                          
                                      
                              
                                                                
        
                                 
                                                              
                                     
                                            
        
                                    
                                               
                                 
                                            
        
                                      
                            
                                                               
                                                          
                                                            
                                                                  
                
            
                                                          
      
                                                    
                                          
                                                      
                                                                 
                                               

                                                                       
                                                                          
                                           
                                                                           
                                                      
                                                 
                                               
                                                                    
                                          
                          
                                                             
                       
                                                                
                    
                                         
                                                     
                                                            
                                         
                             
             
                                                
                                                 
                               
                                                          
              
            

                                                                        
                                                                             
                                                      
                               
                                         
                                                          
                                                       
                                                                    
                            
                                               
                     
                                                            
                                     
                      
              
                                 
                                   
                                                        
                                                          
                                                                         
               
                                 
                               
                                             
                          
                              
                   
                               
            
                                                          
                                                                
                                                                  
                                                     
                                   
                  
                                               
                                                                         
                                               
                                                  
            
                                                          
                                                                
                                                                  
                                                     
                                   
                  
                                                                         
                                               
                                               
                                                  
                             
      
                                                 
                                    
                                                        
                                                          
                                                             
                                                     
                                      
                                                          
                                                            
                                                                
                     
                                     
                                                    
                                                        
                                                          
                                                                 
                             
                
                           
                                                    
                                     
                                                        
                                                          
                                                                 
                             
                
                             
                
                           
                                                                   
                                
                       
                                      
                                                                      
                     
          
                                                          
          
                                  
                         
                                                              
                            
                    
                                                                
                                          
                          
                    
                      
                                                                   

                                                                        
                                                           
                                                           
                          
                                                      
                                                           
                          
                                                                     
                         
                                           
                                                                            
                                    
                               
                                                     
                                                            
                                                         
                                      
                       
                                              
                                                            
                                                     
        
                                       
                                                
                              
                                      
                                          
                                          
                             
             
                                                
                                                 
                               
                                                          
                                                                 
      
                                       
                               
                                        
                                   
                                                  
            
                                         

end GuthMaynard.NativeMoment

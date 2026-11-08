module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.OriginRegularization
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.PositiveSideJetSeminorms

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff Topology
open MeasureTheory Filter

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma iteratedDeriv_eq_zero_of_lt_support (b : ℝ) (h : ℝ → ℂ)
    (hpos : PositiveSideSupport b h) (m : ℕ) :
    ∀ x : ℝ, b < x → iteratedDeriv m h x = 0 := by
  induction m with
  | zero => intro x hx; simpa using hpos x hx
  | succ m ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have h1 : iteratedDeriv m h =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) (fun y hy => ih y hy)
    simpa using h1.deriv_eq

private lemma norm_iteratedDeriv_le_S (b : ℝ) (hb : 0 < b) (m : ℕ) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) {x : ℝ} (hx : x ∈ Set.Icc 0 b) :
    ‖iteratedDeriv m h x‖ ≤ S b m h := by
  have hfin := S_finite b hb m h hh
  have hterm : ‖iteratedDeriv m h x‖ ≤
      sSup ((fun y : ℝ => ‖iteratedDeriv m h y‖) '' Set.Icc 0 b) :=
    le_csSup (hfin m (Finset.mem_range.mpr (Nat.lt_succ_self m)))
      (Set.mem_image_of_mem _ hx)
  have hnonneg : ∀ i ∈ Finset.range (m + 1),
      0 ≤ sSup ((fun y : ℝ => ‖iteratedDeriv i h y‖) '' Set.Icc 0 b) := by
    intro i hi
    exact le_trans (norm_nonneg _)
      (le_csSup (hfin i hi) (Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr hb.le)))
  have hsingle : sSup ((fun y : ℝ => ‖iteratedDeriv m h y‖) '' Set.Icc 0 b) ≤ S b m h := by
    rw [S]
    exact Finset.single_le_sum hnonneg (Finset.mem_range.mpr (Nat.lt_succ_self m))
  exact hterm.trans hsingle

private lemma norm_mellin_le (b : ℝ) (hb : 0 < b) (m : ℕ) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hpos : PositiveSideSupport b h) (s : ℂ) (hs : 0 < s.re) :
    ‖mellin (iteratedDeriv m h) s‖ ≤ S b m h * b ^ s.re / s.re := by
  set g : ℝ → ℂ := iteratedDeriv m h with hg
  set σ : ℝ := s.re with hσ
  have hσpos : 0 < σ := by rw [hσ]; exact hs
  have hSnn : 0 ≤ S b m h := S_nonneg b hb m h hh
  have hgcont : Continuous g := by
    rw [hg]; exact hh.continuous_iteratedDeriv m (by simp)
  set F : ℝ → ℝ := Set.indicator (Set.Ioc (0 : ℝ) b) (fun t => S b m h * t ^ (σ - 1)) with hF
  have hFapply : ∀ t : ℝ, F t = if t ∈ Set.Ioc (0 : ℝ) b then S b m h * t ^ (σ - 1) else 0 := by
    intro t; rw [hF]; exact Set.indicator_apply ..
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • g t‖ ≤ F t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hnorm : ‖(t : ℂ) ^ (s - 1) • g t‖ = t ^ (σ - 1) * ‖g t‖ := by
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
    rw [hnorm]
    by_cases htb : t ≤ b
    · have htmem : t ∈ Set.Ioc (0 : ℝ) b := ⟨ht0, htb⟩
      rw [hFapply t, if_pos htmem]
      have hgt : ‖g t‖ ≤ S b m h := by
        rw [hg]
        exact norm_iteratedDeriv_le_S b hb m h hh ⟨ht0.le, htb⟩
      calc t ^ (σ - 1) * ‖g t‖ ≤ t ^ (σ - 1) * S b m h := by gcongr
        _ = S b m h * t ^ (σ - 1) := by ring
    · have hnotmem : t ∉ Set.Ioc (0 : ℝ) b := fun hmem => htb hmem.2
      rw [hFapply t, if_neg hnotmem]
      have hg0 : g t = 0 := by
        rw [hg]
        exact iteratedDeriv_eq_zero_of_lt_support b h hpos m t (lt_of_not_ge htb)
      rw [hg0, norm_zero, mul_zero]

  have hφint : IntegrableOn (fun t : ℝ => S b m h * t ^ (σ - 1)) (Set.Ioc (0 : ℝ) b) := by
    have h1 : IntervalIntegrable (fun t : ℝ => t ^ (σ - 1)) volume (0 : ℝ) b :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    exact h1.1.const_mul (S b m h)
  have hFint : Integrable F volume := by
    rw [hF]
    exact (integrable_indicator_iff measurableSet_Ioc).2 hφint
  have hFintOn : IntegrableOn F (Set.Ioi (0 : ℝ)) volume := hFint.integrableOn

  have hFint_eq : ∫ t in Set.Ioi (0 : ℝ), F t = S b m h * b ^ σ / σ := by
    have h1 : ∫ t in Set.Ioi (0 : ℝ), F t = ∫ t, F t :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hFapply x, if_neg]
        intro hmem
        exact hx hmem.1)
    have h2 : ∫ t, F t = ∫ t in Set.Ioc (0 : ℝ) b, (fun t : ℝ => S b m h * t ^ (σ - 1)) t := by
      rw [hF]
      exact integral_indicator measurableSet_Ioc
    have h3 : ∫ t in Set.Ioc (0 : ℝ) b, (fun t : ℝ => S b m h * t ^ (σ - 1)) t
        = ∫ t in (0 : ℝ)..b, (fun t : ℝ => S b m h * t ^ (σ - 1)) t :=
      (intervalIntegral.integral_of_le hb.le).symm
    have h4 : ∫ t in (0 : ℝ)..b, (fun t : ℝ => S b m h * t ^ (σ - 1)) t
        = S b m h * ∫ t in (0 : ℝ)..b, t ^ (σ - 1) :=
      intervalIntegral.integral_const_mul (S b m h) (fun t : ℝ => t ^ (σ - 1))
    have h5 : ∫ t in (0 : ℝ)..b, t ^ (σ - 1) = b ^ σ / σ := by
      rw [integral_rpow (Or.inl (by linarith))]
      have hσ' : σ - 1 + 1 = σ := by ring
      rw [hσ', Real.zero_rpow (ne_of_gt hσpos)]
      simp
    rw [h1, h2, h3, h4, h5]
    ring

  have hcont_cpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Set.Ioi (0 : ℝ)) :=
    fun t ht => (Complex.continuousAt_ofReal_cpow_const t (s - 1)
      (Or.inr (ne_of_gt ht))).continuousWithinAt
  have hint : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • g t‖)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine Integrable.mono' hFintOn ?_ ?_
    · exact (hcont_cpow.smul hgcont.continuousOn).norm.aestronglyMeasurable measurableSet_Ioi
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall (fun t ht => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hpt t ht)
  have hle : (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • g t‖) ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] F :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (fun t ht => hpt t ht))
  calc ‖mellin g s‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • g t‖ := by
        rw [mellin]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), F t := setIntegral_mono_ae_restrict hint hFintOn hle
    _ = S b m h * b ^ σ / σ := hFint_eq

                                                                                               
                      
                                                             
                             
                                                                                   
                                                                
                                                  
                                 
                                                           
                                                                           
                                                               
                                  
            

                                                                                  
                                   
                                                         
                                                           

                              
                                                               
                                                        
                          
                                                                       
                                                     
              
                
                                                             
                               
                                                    
                         
                                    
                                                       
                                                   
                                          
                                 
                                                 
                                                                
                                                                  
                                                     
                                                                    
                                                                         
                                                                   
                                                              
                                                      
                                                            
                                                        
                                                       
                                                                 
                                  
                                                            
                                         
                                                                    
                                                          
                               
                                                     
            
                                          
                                                                
                                                                                           
                                           
                                                                                               
                                                  
                                                                                                 
                                                 
                                                                                                   
                                                                     
                                                         
                                                                                                      
                    
                                   
                                                                                    
                                                                                               
                                                                      
                                             
                                                                                                
                                           
                                                                                   
                                                     
                          
                                                                    
                                                        

                                                               
                                    
                             
                                                         
                                 
                                                                  
                           
                                                                
                                         
                                                                
                                         
                                                                                      
                           
                                                                      

                                                                 
                
                             
                                                         
                                 
                                                      
                                                   
                                                                       
                                                             
                                                               
                                                    
           
                 
                
                                                       
                                         
                            
                              
                                   
                           
                                                   
                                                                           
                                                                           
                                                
                                                                      
             
                                                                
                                                                                            
                        
                                                                                        

end DedekindZetaZeroFree.LargeSieve.Vendor

end

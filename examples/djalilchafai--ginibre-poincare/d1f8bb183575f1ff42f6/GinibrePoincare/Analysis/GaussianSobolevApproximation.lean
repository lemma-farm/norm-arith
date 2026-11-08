module

public import GinibrePoincare.Analysis.RadialSobolevClosure
public import GinibrePoincare.Analysis.SobolevTruncation
public import GinibrePoincare.Analysis.BernoulliTaylorEnergy
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace GinibrePoincare
noncomputable section

/-- Mollification approximates both a compact C¹ function and its derivative
uniformly; the approximant is genuinely smooth and compactly supported. -/
theorem exists_smooth_compact_C1_approximation (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ x, |g x - f x| ≤ ε) ∧ (∀ x, |deriv g x - deriv f x| ≤ ε) := by
  have huf := hf.continuous.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty
  have hdf := hf.continuous_deriv le_rfl
  have hud := hdf.uniformContinuous_of_tendsto_cocompact hc.deriv.is_zero_at_infty
  obtain ⟨δf, hδf, hff⟩ := Metric.uniformContinuous_iff.mp huf ε hε
  obtain ⟨δd, hδd, hdd⟩ := Metric.uniformContinuous_iff.mp hud ε hε
  let δ := min δf δd
  have hδ : 0 < δ := lt_min hδf hδd
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let g := φ.normed volume ⋆[lsmul ℝ ℝ, volume] f
  have hg : ContDiff ℝ ∞ g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hf.continuous.locallyIntegrable
  have hdg (x : ℝ) : deriv g x =
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] deriv f) x :=
    (hc.hasDerivAt_convolution_right _ (φ.contDiff_normed (n := ⊤)).continuous.locallyIntegrable hf x).deriv
  refine ⟨g, hg, φ.hasCompactSupport_normed.convolution _ hc, ?_, ?_⟩
  · intro x
    have h := φ.dist_normed_convolution_le (μ := volume) (x₀ := x) hf.continuous.aestronglyMeasurable
      (fun y hy => (hff ((Metric.mem_ball.mp hy).trans_le (min_le_left _ _))).le)
    simpa only [Real.dist_eq, g] using h
  · intro x
    rw [hdg]
    have h := φ.dist_normed_convolution_le (μ := volume) (x₀ := x) hdf.aestronglyMeasurable
      (fun y hy => (hdd ((Metric.mem_ball.mp hy).trans_le (min_le_right _ _))).le)
    simpa only [Real.dist_eq] using h

/-- Uniform errors control the actual L² distance under a probability law. -/
theorem L2_toLp_dist_le_of_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ x, |f x - g x| ≤ ε) :
    dist (hf.toLp f) (hg.toLp g) ≤ ε := by
  rw [dist_eq_norm]
  have hb : ∀ᵐ x ∂μ, ‖(hf.toLp f - hg.toLp g) x‖ ≤ ε := by
    filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
      with x hx hfx hgx
    simpa only [hx, Pi.sub_apply, hfx, hgx, Real.norm_eq_abs] using he x
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hε hb

/-- The L² distance is the square root of the squared representative error. -/
theorem L2_toLp_dist_eq_sqrt_error (μ : Measure ℝ) (f g : ℝ → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) = Real.sqrt (∫ x, (f x - g x) ^ 2 ∂μ) := by
  have he : (∫ x, (f x - g x) ^ 2 ∂μ) = ‖hf.toLp f - hg.toLp g‖ ^ 2 := by
    rw [← integral_square_eq_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
      with x hx hfx hgx
    simp only [hx, Pi.sub_apply, hfx, hgx]
  rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), dist_eq_norm]

/-- Actual compact C¹ value-derivative pairs in weighted L². -/
def compactC1SobolevPairs (μ : Measure ℝ) : Set (Lp ℝ 2 μ × Lp ℝ 2 μ) :=
  {p | ∃ f : ℝ → ℝ, ContDiff ℝ 1 f ∧ HasCompactSupport f ∧
    (p.1 : ℝ → ℝ) =ᵐ[μ] f ∧ (p.2 : ℝ → ℝ) =ᵐ[μ] deriv f}

/-- Actual compact C² value-derivative pairs in weighted L². -/
def compactC2SobolevPairs (μ : Measure ℝ) : Set (Lp ℝ 2 μ × Lp ℝ 2 μ) :=
  {p | ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
    (p.1 : ℝ → ℝ) =ᵐ[μ] f ∧ (p.2 : ℝ → ℝ) =ᵐ[μ] deriv f}

                                                                          
                                                                             
                                     
                                                                                                

                                                                                      
theorem compactC1SobolevPairs_subset_closure_C2 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    compactC1SobolevPairs μ ⊆ closure (compactC2SobolevPairs μ) := by
  intro p hp
  obtain ⟨f, hf, hc, hv, hd⟩ := hp
  have hfv := hf.continuous.memLp_of_hasCompactSupport (μ := μ) hc (p := 2)
  have hfd := (hf.continuous_deriv le_rfl).memLp_of_hasCompactSupport (μ := μ) hc.deriv (p := 2)
  have hpv : p.1 = hfv.toLp f := Lp.ext (hv.trans hfv.coeFn_toLp.symm)
  have hpd : p.2 = hfd.toLp (deriv f) := Lp.ext (hd.trans hfd.coeFn_toLp.symm)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hg, hgc, hgv, hgd⟩ := exists_smooth_compact_C1_approximation f hf hc (half_pos hε)
  have hgvLp := hg.continuous.memLp_of_hasCompactSupport (μ := μ) hgc (p := 2)
  have hgdLp := (hg.continuous_deriv (by simp)).memLp_of_hasCompactSupport (μ := μ) hgc.deriv (p := 2)
  let q : Lp ℝ 2 μ × Lp ℝ 2 μ := (hgvLp.toLp g, hgdLp.toLp (deriv g))
  refine ⟨q, ⟨g, (show ContDiff ℝ 2 g from hg.of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))), hgc, hgvLp.coeFn_toLp, hgdLp.coeFn_toLp⟩, ?_⟩
  rw [Prod.dist_eq]
  apply max_lt
  · rw [hpv, dist_comm]
    exact (L2_toLp_dist_le_of_uniform μ g f hgvLp hfv (half_pos hε).le hgv).trans_lt (half_lt_self hε)
  · rw [hpd, dist_comm]
    exact (L2_toLp_dist_le_of_uniform μ (deriv g) (deriv f) hgdLp hfd
      (half_pos hε).le hgd).trans_lt (half_lt_self hε)

/-- Compact C¹ and C² cores have exactly the same weighted H¹ completion. -/
theorem closure_compactC1SobolevPairs_eq_C2 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    closure (compactC1SobolevPairs μ) = closure (compactC2SobolevPairs μ) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (compactC1SobolevPairs_subset_closure_C2 μ) isClosed_closure
  · apply closure_mono
    intro p hp
    obtain ⟨f, hf, hc, hv, hd⟩ := hp
    exact ⟨f, hf.of_le (by norm_num), hc, hv, hd⟩


/-- Truncation puts every finite-energy C¹ function into the weighted H¹ completion. -/
theorem C1_pair_mem_sobolev_completion (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hv : MemLp f 2 μ) (hd : MemLp (deriv f) 2 μ) :
    (hv.toLp f, hd.toLp (deriv f)) ∈ closure (compactC1SobolevPairs μ) := by
  let F : ℕ → ℝ → ℝ := fun n x => sobolevCutoff n x * f x
  have hF (n : ℕ) : ContDiff ℝ 1 (F n) :=
    ((sobolevCutoff_smooth n).of_le (by simp)).mul hf
  have hcF (n : ℕ) : HasCompactSupport (F n) := (sobolevCutoff_compact n).mul_right
  have hvF (n : ℕ) : MemLp (F n) 2 μ := (hF n).continuous.memLp_of_hasCompactSupport (hcF n)
  have hdF (n : ℕ) : MemLp (deriv (F n)) 2 μ :=
    ((hF n).continuous_deriv le_rfl).memLp_of_hasCompactSupport (hcF n).deriv
  let P : ℕ → Lp ℝ 2 μ × Lp ℝ 2 μ :=
    fun n => ((hvF n).toLp (F n), (hdF n).toLp (deriv (F n)))
  have ht := sobolevCutoff_L2_errors_tendsto μ f hf hv hd
  have htv : Tendsto (fun n => (P n).1) atTop (𝓝 (hv.toLp f)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    change Tendsto (fun n => dist ((hvF n).toLp (F n)) (hv.toLp f)) atTop (𝓝 0)
    simp_rw [L2_toLp_dist_eq_sqrt_error]
    simpa [F] using ht.1.sqrt
  have htd : Tendsto (fun n => (P n).2) atTop (𝓝 (hd.toLp (deriv f))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    change Tendsto (fun n => dist ((hdF n).toLp (deriv (F n))) (hd.toLp (deriv f))) atTop (𝓝 0)
    simp_rw [L2_toLp_dist_eq_sqrt_error]
    simpa [F] using ht.2.sqrt
  apply isClosed_closure.mem_of_tendsto (htv.prodMk_nhds htd)
  apply Eventually.of_forall
  intro n
  exact subset_closure ⟨F n, hF n, hcF n, (hvF n).coeFn_toLp, (hdF n).coeFn_toLp⟩

                                                                              
                                                                                
                                                                       
                                                                                     
                                                                            
                                            
                                                   

                                                                                    
                                      
                                                                
                                                            
                                                                       
                               
                                                                                                   
                                                                                    
                             
                                          
                                
            
                                  
             
                                                                                    
                                                                                         
                                 
             
                                                                     
                                                                    
                                                                      
                             
                                   
               
           
                       

                                                                        
                                                        
                                               
                                                                                                   
                                     
                                                                                                        
                                                                               
                                 
                                    
                                            
          

                                                                          
                                                                                        
                             
                                                                
                                                            
                                                                     
                                     
                                                         
                                                                   
                                                                                             
                                                            
                                                                          
                                                                               
                                                 
             
                   
                                            
             
                  
                                                                                      
                                                                                     
                                                                      
                             
                                              
               
                  
            

end
end GinibrePoincare

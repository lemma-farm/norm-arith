module

public import RequestProject.ReconBasic
public import RequestProject.BoundaryChart
public import RequestProject.ArcLength

/-!
# Lipschitz extension of boundary traces

For a bounded Lipschitz domain `Ω` with boundary parametrization `γ`, the parametrization is
bi-Lipschitz onto `∂Ω` (with respect to the distance on the circle, `chord_arc`), so every
closed Lipschitz function `h` on `[0, 2π]` is the trace `V ∘ γ` of a Lipschitz compactly
supported `V : ℂ → ℂ` (`exists_lipschitz_extension_of_trace`).

The chord-arc estimate is proved locally in a boundary chart: there the boundary is a Lipschitz
graph, the abscissa `x(s)` of `γ(s)` is strictly monotone, and the constant speed of `γ`
together with the cone condition `|γ'| ≤ (1 + K)|x'|` gives `|x'| ≥ c₀/(1 + K)`. A compactness
argument makes the estimate global.
-/

@[expose] public section

open MeasureTheory Set Filter Metric Topology
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

                                                                                              
                                             
                                     
                                            
                                           
                       
                                                                    

                                                                                             
                                    
                                             
                                     
                                       
                                                                                    
                                                                                      
                                                    
                                                                          
                                                     
                         
                                
                                                                               
                                        
             
                        
                                           
                                    
                
            
          

/-- **Lower bound in a cone.** If, on an interval, a constant-speed Lipschitz curve satisfies the
cone condition `‖γ s - γ s'‖ ≤ L |Re(c(γ s - γ s'))|` and `Re(c γ)` is strictly increasing, then
`Re(c γ)` grows at least at rate `c₀ / L`. -/
lemma lower_bound_of_cone {Kγ : NNReal} (hK : LipschitzWith Kγ γ) {a b : ℝ} {c : ℂ} {L c0 : ℝ}
    (hL : 0 < L) (hspeed : ∀ᵐ θ, ‖deriv γ θ‖ = c0)
    (hcone : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, ‖γ s - γ s'‖ ≤ L * |(c * (γ s - γ s')).re|)
    (hmono : StrictMonoOn (fun s => (c * γ s).re) (Ioo a b)) {s s' : ℝ} (hs : s ∈ Ioo a b)
    (hs' : s' ∈ Ioo a b) (hss : s ≤ s') :
    c0 / L * (s' - s) ≤ (c * (γ s' - γ s)).re := by
  have hpt : ∀ u ∈ Ioo a b, ∀ v, HasDerivAt γ v u → ‖v‖ ≤ L * |(c * v).re| ∧ 0 ≤ (c * v).re := by
    intro u hu v hv
    have ht := hv.tendsto_slope_zero
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), u + t ∈ Ioo a b := by
      have : Tendsto (fun t : ℝ => u + t) (𝓝 0) (𝓝 u) := by
        simpa using (continuous_const_add u).tendsto (0 : ℝ)
      exact nhdsWithin_le_nhds (this (isOpen_Ioo.mem_nhds hu))
    have hcre : Continuous fun v : ℂ => (c * v).re :=
      Complex.continuous_re.comp (continuous_const.mul continuous_id)
    constructor
    · refine (isClosed_le continuous_norm (continuous_const.mul hcre.abs)).mem_of_tendsto ht ?_
      filter_upwards [hev] with t ht1
      show ‖t⁻¹ • (γ (u + t) - γ u)‖ ≤ L * |(c * (t⁻¹ • (γ (u + t) - γ u))).re|
      rw [norm_smul, Complex.real_smul, mul_left_comm, Complex.re_ofReal_mul, abs_mul,
        Real.norm_eq_abs]
      have := mul_le_mul_of_nonneg_left (hcone _ ht1 u hu) (abs_nonneg t⁻¹)
      linarith
    · refine (isClosed_le continuous_const hcre).mem_of_tendsto ht ?_
      filter_upwards [hev, self_mem_nhdsWithin] with t ht1 ht0
      show 0 ≤ (c * (t⁻¹ • (γ (u + t) - γ u))).re
      rw [Complex.real_smul, mul_left_comm, Complex.re_ofReal_mul, mul_sub, Complex.sub_re]
      rcases lt_or_gt_of_ne (show t ≠ 0 from ht0) with hneg | hpos
      · have : (c * γ (u + t)).re < (c * γ u).re := hmono ht1 hu (by linarith)
        exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr hneg.le) (by linarith)
      · have : (c * γ u).re < (c * γ (u + t)).re := hmono hu ht1 (by linarith)
        exact mul_nonneg (inv_nonneg.mpr hpos.le) (by linarith)
  have hae : ∀ᵐ u, u ∈ Ioo a b → c0 / L ≤ (c * deriv γ u).re := by
    filter_upwards [hK.ae_differentiableAt, hspeed] with u hd hsp hu
    obtain ⟨h1, h2⟩ := hpt u hu _ hd.hasDerivAt
    rw [hsp, abs_of_nonneg h2] at h1
    rw [div_le_iff₀ hL]
    linarith
  have hd : IntervalIntegrable (fun u => (c * deriv γ u).re) volume s s' := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hss).mpr ?_
    refine Measure.integrableOn_of_bounded (M := ‖c‖ * Kγ) measure_Ioc_lt_top.ne
      (Complex.measurable_re.comp ((measurable_deriv γ).const_mul c)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    gcongr
    exact norm_deriv_le_of_lipschitz hK
  have hftc : (c * (γ s' - γ s)).re = ∫ u in s..s', (c * deriv γ u).re := by
    rw [← integral_deriv_of_lipschitz hK s s', ← intervalIntegral.integral_const_mul]
    have := (Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) hss).mpr
        (Measure.integrableOn_of_bounded (μ := volume) (M := Kγ) measure_Ioc_lt_top.ne
          (measurable_deriv γ).aestronglyMeasurable
          (Eventually.of_forall fun u => norm_deriv_le_of_lipschitz hK))).const_mul c))
    simpa using this.symm
  rw [hftc]
  have hconst : ∫ _ in s..s', c0 / L = c0 / L * (s' - s) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  rw [← hconst]
  refine intervalIntegral.integral_mono_ae_restrict hss intervalIntegrable_const hd ?_
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hae] with u hu hu'
  exact hu ⟨by linarith [hs.1, hu'.1], by linarith [hs'.2, hu'.2]⟩

                                    
                                                                                      
                                                                                 
                                        
                                  
                                            
                               
                                                                     
                            
                                                   
                                                                                     
                                               
                                                        
                                 
                                                  
                                      
                                          
                                           
                                                                         
                                                                               
                                                                                        
                     
                                                                                    
                           
                                                                                         
                                               
                   
                                                                           
                                                                                 
                                                   
                        
                                                                   
                                         
                     
             
                                                                                              
                                                     
                                                        
                                                                                   
                                             
                                           
                                                     
                                                          
                                               
                                                                     
                                          
                                                     
                                                                   
                                       
                                                                         
                                                                  
                              
                                                                         
                                      
                              
                                                    
                                                                        
                           
                                                                                              
                                                                    
                                                         
                         

                                                                         
                                                              

                                                                                             
        
                                                                         
                                                                                              
                                  
                                             
                                                     
                                                                       
                                                                                         
                                                                       
                                                       
              
                                                  
                                      
                                                                       
                                   
                              
                                            
                  
                                       
                                                                       
               
                                                                
                                            
                       
                               
                                              
                                                                                        
                                                                                  
                          
              
                                                               
                             
                                                                                            
                           
                                                                                     
                                                              
                                    
                                                                   
                                               
                                                                     
                                                                    
                                                         
                                                                   
                
           
                                                                          
                                  
                                             
                                         
                                                                        
                                       
                                
                                          
                                                
                               
                                             
                                                                                       
                                    
                   
                                   
                                                                                
                                        
                   
                                     
                                                                    
                                   
                                                                          
                                                               
                            
                                                      
                    
                             
                                          
                                                                                        
                                                                                     
                                                                                            
                       
                                            
                                                                                         
                                           
                                                        
                                                                                     
              
                                                 
                                                                                     
              
                                                     
                             
                                                                   
                                        
                                                                                      
                                                                                            
                       
                                

                                                                                     
                                                                                              
                                                                                             
                                          
                                             
                                                                                              
                       
                                      
                                              
                                                             
                                                           
                 
                                                  
                                   
                                     
                                                                                
          
                                     
                           
                                   
                                    
                                           
                                                  
             
                                                                                
          
                                     
                                 
                             
                                    
                                                 
                                                     
             

                                                                                                
                             
                                                                                                                                     
                                                                                      
                                                                            
                                              
           
                                  
                                        
                                             
                                             
                                                              
                                                           
                                                                                
                                               
                              
                                     
                                                                      
                                            
                     
                                                         
                           
                                                
                                                                         
                                       
                                                 
                                                                  
              
                                              
                                       
                                                             
                                                   
                                        
                                                
                                                                    
                                 
                                            
                                                                
                   
                 
                                                
                                
                               
                                                                 
                                                    
                                        
              
                              
                             
                                                                   
                   
                                                         
                                             
                                
                                  
                                 
                                      
                                                                      
                                                                   
                      
                                    
                                                            
                                                                            
                                                                   
                                
                                    
                                                            
                             
                                                                                      
                                                                    
                                                                    
                                      
                
                                      
                                                            
                                                             
                                                     
                                                             
                                                            
                                                             
                                                     
                                                             
                                           
                                           
                                                                             
                                                     
                     
                                                                                          
                                                                                           
          
                                     
                                                                                
                                  
                                  
                              
                                           
             
            
                                                                                        
                                                      
                                    
                       
                       
                                                                                      
                   
        
              
                                              
                                   
                       
                       
                                                  
                                                          
                   
                                 

end PolyaNeumann

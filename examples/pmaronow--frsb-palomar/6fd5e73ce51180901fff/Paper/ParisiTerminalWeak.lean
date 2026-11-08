module

public import Paper.ParisiDuhamelWeak
public import Paper.HeatGrowth
public import Mathlib
@[expose] public section

/-! # The linearly growing terminal term in the weak Parisi equation

The terminal datum is `log cosh`.  Spatial self-adjointness and the heat
operator's first absolute moment justify the terminal heat identity without
assuming that this datum is bounded.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem continuous_logcosh : Continuous (fun x : ℝ => Real.log (Real.cosh x)) :=
  Real.continuous_cosh.log (fun x => (Real.cosh_pos x).ne')

theorem integrable_logcosh_heatTest (β : ℝ) (ψ : ℝ × ℝ → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun p : ℝ × ℝ => Real.log (Real.cosh p.2) *
      heatSemigroup (β ^ 2 * (1 - p.1)) (fun y => ψ (p.1, y)) p.2)
      (parisiTimeMeasure.prod volume) := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_integral_norm_sections_bound ψ hψ hc
  let χ : ℝ × ℝ → ℝ := fun p => ‖p.2‖ * ψ p
  have hχ : Continuous χ := by unfold χ; fun_prop
  have hχc : HasCompactSupport χ := hc.mul_left
  obtain ⟨D, _hD0, hD⟩ := exists_uniform_integral_norm_sections_bound χ hχ hχc
  have hψmeas : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      ψ (p.1.1, p.1.2 + Real.sqrt (β ^ 2 * (1 - p.1.1)) * p.2)) :=
    hψ.measurable.comp (by fun_prop)
  have hh := (hψmeas.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hp : Measurable (fun p : ℝ × ℝ => Real.log (Real.cosh p.2) *
      heatSemigroup (β ^ 2 * (1 - p.1)) (fun y => ψ (p.1, y)) p.2) :=
    (continuous_logcosh.comp continuous_snd).measurable.mul hh
  have hsections (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) := by
    have hψi : Integrable (fun x : ℝ => ψ (t, x)) :=
      (hψ.comp (by fun_prop)).integrable_of_hasCompactSupport
        (hasCompactSupport_spatial_section ψ hc t)
    have hχi : Integrable (fun x : ℝ => ‖x‖ * ψ (t, x)) :=
      (hχ.comp (by fun_prop)).integrable_of_hasCompactSupport
        (hasCompactSupport_spatial_section χ hχc t)
    have hweighted : Integrable (fun x : ℝ => ‖x‖ * ‖ψ (t, x)‖) := by
      simpa only [norm_mul, norm_norm] using hχi.norm
    exact heatSemigroup_firstMoment (β ^ 2 * (1 - t))
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2)) (fun y => ψ (t, y))
      ((hψ.comp (by fun_prop)).measurable) hψi hweighted
  have hbound (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      (∫ x, ‖Real.log (Real.cosh x) *
        heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x‖) ≤
        D + |β| * gaussianAbsMoment * B := by
    have hheat := hsections t ht
    have hi : Integrable (fun x : ℝ => Real.log (Real.cosh x) *
        heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x) := by
      apply hheat.1.norm.mono'
        ((hp.comp (show Measurable (fun x : ℝ => (t, x)) by fun_prop)).aestronglyMeasurable)
      filter_upwards with x
      change ‖Real.log (Real.cosh x) * heatSemigroup (β ^ 2 * (1 - t))
        (fun y => ψ (t, y)) x‖ ≤ ‖‖x‖ * heatSemigroup (β ^ 2 * (1 - t))
        (fun y => ψ (t, y)) x‖
      simp only [norm_mul, norm_norm]
      have hl : ‖Real.log (Real.cosh x)‖ ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using (norm_logcosh_le_abs x)
      exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
    have hsq : Real.sqrt (β ^ 2 * (1 - t)) ≤ |β| := by
      calc
        _ ≤ Real.sqrt (β ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg β, ht.1.le])
        _ = _ := Real.sqrt_sq_eq_abs β
    calc
      _ ≤ ∫ x, ‖x‖ * ‖heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x‖ := by
        apply integral_mono hi.norm
          (by simpa only [norm_mul, norm_norm] using hheat.1.norm)
        intro x
        dsimp only
        rw [norm_mul]
        have hl : ‖Real.log (Real.cosh x)‖ ≤ ‖x‖ := by
          simpa only [Real.norm_eq_abs] using (norm_logcosh_le_abs x)
        exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
      _ ≤ _ := hheat.2
      _ ≤ D + |β| * gaussianAbsMoment * B := by
        have hDw : (∫ x, ‖x‖ * ‖ψ (t, x)‖) ≤ D := by
          simpa only [χ, norm_mul, norm_norm] using hD t
        calc
          _ ≤ D + Real.sqrt (β ^ 2 * (1 - t)) * gaussianAbsMoment * B :=
            add_le_add hDw (mul_le_mul_of_nonneg_left (hB t)
              (mul_nonneg (Real.sqrt_nonneg _) gaussianAbsMoment_nonneg))
          _ ≤ _ := add_le_add (le_refl D)
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsq gaussianAbsMoment_nonneg) hB0)
  apply (integrable_prod_iff hp.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply (hsections t ht).1.norm.mono'
      ((hp.comp (show Measurable (fun x : ℝ => (t, x)) by fun_prop)).aestronglyMeasurable)
    filter_upwards with x
    change ‖Real.log (Real.cosh x) * heatSemigroup (β ^ 2 * (1 - t))
      (fun y => ψ (t, y)) x‖ ≤ ‖‖x‖ * heatSemigroup (β ^ 2 * (1 - t))
      (fun y => ψ (t, y)) x‖
    simp only [norm_mul, norm_norm]
    have hl : ‖Real.log (Real.cosh x)‖ ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using (norm_logcosh_le_abs x)
    exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
  · apply (integrable_const (D + |β| * gaussianAbsMoment * B)).mono'
      (hp.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using hbound t ht

                                                               
                                                                         

                                                                                    
                                       
                                                                             

                                                                      
                                                                    
                                                  
                                                            
                                       
                                                     
                                  
                                                                 
                                                                                   
                                                              
                                        
                                                                                           
                                                   
                         
      
                                           
                                                                                       
                             
                                                                  
                                                      
                                                               
                                                     
                                                                 
                                                                         
                                                                                                 
                                                              
                                                       
                                                
                                                                                          
                                                                      
                                                                                                    
                                                         
                                                                    
                                    
                                                                           
                           
         
                                                       
             
              
                                    
                                                                                            
                                                 

end Paper

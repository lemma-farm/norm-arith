module
public import Paper.GaussianHeat
public import Paper.GaussianConvolution
public import Mathlib

@[expose] public section

/-!
# A Gaussian Poincaré proof by rotation

The analytic foundation is derived from dominated differentiation and the
proved one-dimensional Stein identity. No Poincaré inequality is postulated.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

lemma integrable_gaussian_pair_bounded (F : ℝ × ℝ → ℝ) (C : ℝ)
    (hF : Continuous F) (hb : ∀ p, ‖F p‖ ≤ C) : Integrable F standardGaussianPair := by
  exact (integrable_const C).mono' hF.aestronglyMeasurable (.of_forall hb)

lemma integrable_gaussian_pair_coordinate_mul (F : ℝ × ℝ → ℝ) (C : ℝ)
    (hF : Continuous F) (hb : ∀ p, ‖F p‖ ≤ C) :
    Integrable (fun p => p.1 * F p) standardGaussianPair ∧
      Integrable (fun p => p.2 * F p) standardGaussianPair := by
  exact ⟨(integrable_standardGaussian_id.comp_fst (gaussianReal 0 1)).mul_bdd
    hF.aestronglyMeasurable (.of_forall hb),
    (integrable_standardGaussian_id.comp_snd (gaussianReal 0 1)).mul_bdd
    hF.aestronglyMeasurable (.of_forall hb)⟩

/-- Stein's identity in the first coordinate of two independent normals. -/
theorem gaussian_pair_stein_fst (F dF : ℝ × ℝ → ℝ) (M K : ℝ)
    (hF : Continuous F) (hdF : Continuous dF)
    (hd : ∀ p, HasDerivAt (fun z => F (z, p.2)) (dF p) p.1)
    (hb : ∀ p, ‖F p‖ ≤ M) (hdb : ∀ p, ‖dF p‖ ≤ K) :
    (∫ p, p.1 * F p ∂standardGaussianPair) = ∫ p, dF p ∂standardGaussianPair := by
  simp only [standardGaussianPair]
  rw [integral_prod_symm _ (integrable_gaussian_pair_coordinate_mul F M hF hb).1,
    integral_prod_symm _ (integrable_gaussian_pair_bounded dF K hdF hdb)]
  apply integral_congr_ae
  filter_upwards [] with w
  exact gaussian_stein_of_bounded (fun z => F (z, w)) (fun z => dF (z, w)) M K
    (hF.comp (continuous_id.prodMk continuous_const))
    (hdF.comp (continuous_id.prodMk continuous_const))
    (fun z => hd (z, w)) (fun z => hb (z, w)) (fun z => hdb (z, w))

/-- Stein's identity in the second coordinate. -/
theorem gaussian_pair_stein_snd (F dF : ℝ × ℝ → ℝ) (M K : ℝ)
    (hF : Continuous F) (hdF : Continuous dF)
    (hd : ∀ p, HasDerivAt (fun z => F (p.1, z)) (dF p) p.2)
    (hb : ∀ p, ‖F p‖ ≤ M) (hdb : ∀ p, ‖dF p‖ ≤ K) :
    (∫ p, p.2 * F p ∂standardGaussianPair) = ∫ p, dF p ∂standardGaussianPair := by
  simp only [standardGaussianPair]
  rw [integral_prod _ (integrable_gaussian_pair_coordinate_mul F M hF hb).2,
    integral_prod _ (integrable_gaussian_pair_bounded dF K hdF hdb)]
  apply integral_congr_ae
  filter_upwards [] with z
  exact gaussian_stein_of_bounded (fun w => F (z, w)) (fun w => dF (z, w)) M K
    (hF.comp (continuous_const.prodMk continuous_id))
    (hdF.comp (continuous_const.prodMk continuous_id))
    (fun w => hd (z, w)) (fun w => hb (z, w)) (fun w => hdb (z, w))

/-- Correlation of a function with its Gaussian rotation. -/
def gaussianRotationCovariance (f : ℝ → ℝ) (h a θ : ℝ) : ℝ :=
  ∫ p, f (h + a * p.1) *
    f (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) ∂standardGaussianPair

/-- Differentiation of the actual rotation correlation before applying Stein. -/
theorem hasDerivAt_gaussianRotationCovariance_raw (f df : ℝ → ℝ) (h a θ C : ℝ)
    (hf : Continuous f) (hdf : Continuous df) (hC : 0 ≤ C)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hb : ∀ x, ‖f x‖ ≤ C) (hdb : ∀ x, ‖df x‖ ≤ C) :
    HasDerivAt (gaussianRotationCovariance f h a)
      (∫ p, f (h + a * p.1) * df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) *
        a * (-Real.sin θ * p.1 + Real.cos θ * p.2) ∂standardGaussianPair) θ := by
  let F : ℝ → ℝ × ℝ → ℝ := fun b p => f (h + a * p.1) *
    f (h + a * (Real.cos b * p.1 + Real.sin b * p.2))
  let D : ℝ → ℝ × ℝ → ℝ := fun b p => f (h + a * p.1) *
    df (h + a * (Real.cos b * p.1 + Real.sin b * p.2)) *
      a * (-Real.sin b * p.1 + Real.cos b * p.2)
  have hFc (b : ℝ) : Continuous (F b) := by dsimp [F]; fun_prop
  have hDc (b : ℝ) : Continuous (D b) := by dsimp [D]; fun_prop
  have hFb : ∀ b p, ‖F b p‖ ≤ C ^ 2 := by
    intro b p
    change ‖f (h + a * p.1) *
      f (h + a * (Real.cos b * p.1 + Real.sin b * p.2))‖ ≤ C ^ 2
    rw [norm_mul]
    nlinarith [mul_le_mul (hb (h + a * p.1))
      (hb (h + a * (Real.cos b * p.1 + Real.sin b * p.2)))
      (norm_nonneg _) hC]
  have hDb : ∀ b p, ‖D b p‖ ≤ C ^ 2 * ‖a‖ * (‖p.1‖ + ‖p.2‖) := by
    intro b p
    have htrig : ‖-Real.sin b * p.1 + Real.cos b * p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
      calc
        _ ≤ ‖-Real.sin b * p.1‖ + ‖Real.cos b * p.2‖ := norm_add_le _ _
        _ ≤ ‖p.1‖ + ‖p.2‖ := by
          simp only [norm_mul, norm_neg, Real.norm_eq_abs]
          nlinarith [Real.abs_sin_le_one b, Real.abs_cos_le_one b,
            mul_le_mul_of_nonneg_right (Real.abs_sin_le_one b) (abs_nonneg p.1),
            mul_le_mul_of_nonneg_right (Real.abs_cos_le_one b) (abs_nonneg p.2)]
    change ‖f (h + a * p.1) * df (h + a * (Real.cos b * p.1 + Real.sin b * p.2)) *
      a * (-Real.sin b * p.1 + Real.cos b * p.2)‖ ≤ C ^ 2 * ‖a‖ * (‖p.1‖ + ‖p.2‖)
    simp only [norm_mul]
    have hprod : ‖f (h + a * p.1)‖ *
        ‖df (h + a * (Real.cos b * p.1 + Real.sin b * p.2))‖ ≤ C ^ 2 := by
      nlinarith [mul_le_mul (hb (h + a * p.1))
        (hdb (h + a * (Real.cos b * p.1 + Real.sin b * p.2))) (norm_nonneg _) hC]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hprod (norm_nonneg a)) htrig
      (norm_nonneg _) (mul_nonneg (sq_nonneg C) (norm_nonneg a))
  have hD : ∀ b p, HasDerivAt (fun x => F x p) (D b p) b := by
    intro b p
    have hi := (((Real.hasDerivAt_cos b).mul_const p.1).add
      ((Real.hasDerivAt_sin b).mul_const p.2)).const_mul a |>.const_add h
    convert ((hd _).comp b hi).const_mul (f (h + a * p.1)) using 1
    · rfl
    · dsimp [D]
      ring
  have hIntBound : Integrable (fun p : ℝ × ℝ => C ^ 2 * ‖a‖ * (‖p.1‖ + ‖p.2‖))
      standardGaussianPair := by
    exact ((integrable_standardGaussian_id.norm.comp_fst (gaussianReal 0 1)).add
      (integrable_standardGaussian_id.norm.comp_snd (gaussianReal 0 1))).const_mul _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (bound := fun p => C ^ 2 * ‖a‖ * (‖p.1‖ + ‖p.2‖))
    (s := Set.univ) (by simp) (.of_forall fun b => (hFc b).aestronglyMeasurable)
    (integrable_gaussian_pair_bounded (F θ) _ (hFc θ) (hFb θ))
    (hDc θ).aestronglyMeasurable (.of_forall fun p b _ => hDb b p)
    hIntBound (.of_forall fun p b _ => hD b p)).2

private lemma poincare_mul_bound {C x y : ℝ} (hC : 0 ≤ C)
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x * y‖ ≤ C ^ 2 := by
  rw [norm_mul]
  nlinarith [mul_le_mul hx hy (norm_nonneg y) hC]

/-- The second-derivative terms cancel exactly after two Gaussian Stein
identities. This is the key identity behind Gaussian Poincaré. -/
theorem hasDerivAt_gaussianRotationCovariance (f df ddf : ℝ → ℝ) (h a θ C : ℝ)
    (hf : Continuous f) (hdf : Continuous df) (hddf : Continuous ddf) (hC : 0 ≤ C)
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    (hb : ∀ x, ‖f x‖ ≤ C) (hdb : ∀ x, ‖df x‖ ≤ C) (hddb : ∀ x, ‖ddf x‖ ≤ C) :
    HasDerivAt (gaussianRotationCovariance f h a)
      (-a ^ 2 * Real.sin θ * ∫ p, df (h + a * p.1) *
        df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) ∂standardGaussianPair) θ := by
  let F : ℝ × ℝ → ℝ := fun p => f (h + a * p.1) *
    df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))
  let P : ℝ × ℝ → ℝ := fun p => df (h + a * p.1) *
    df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))
  let Q : ℝ × ℝ → ℝ := fun p => f (h + a * p.1) *
    ddf (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))
  have hFc : Continuous F := by dsimp [F]; fun_prop
  have hPc : Continuous P := by dsimp [P]; fun_prop
  have hQc : Continuous Q := by dsimp [Q]; fun_prop
  have hFb : ∀ p, ‖F p‖ ≤ C ^ 2 := fun p => poincare_mul_bound hC (hb _) (hdb _)
  have hPb : ∀ p, ‖P p‖ ≤ C ^ 2 := fun p => poincare_mul_bound hC (hdb _) (hdb _)
  have hQb : ∀ p, ‖Q p‖ ≤ C ^ 2 := fun p => poincare_mul_bound hC (hb _) (hddb _)
  have hIP := integrable_gaussian_pair_bounded P _ hPc hPb
  have hIQ := integrable_gaussian_pair_bounded Q _ hQc hQb
  have hcoord := integrable_gaussian_pair_coordinate_mul F _ hFc hFb
  have hcos : ‖Real.cos θ‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one θ
  have hsin : ‖Real.sin θ‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one θ
  have hD1c : Continuous (fun p => a * P p + a * Real.cos θ * Q p) := by fun_prop
  have hD1b : ∀ p, ‖a * P p + a * Real.cos θ * Q p‖ ≤ 2 * ‖a‖ * C ^ 2 := by
    intro p
    calc
      _ ≤ ‖a‖ * ‖P p‖ + ‖a‖ * ‖Real.cos θ‖ * ‖Q p‖ := by
        simpa only [norm_mul] using norm_add_le (a * P p) (a * Real.cos θ * Q p)
      _ ≤ ‖a‖ * C ^ 2 + ‖a‖ * 1 * C ^ 2 := by gcongr <;> first | exact hPb p | exact hcos | exact hQb p
      _ = _ := by ring
  have hD2c : Continuous (fun p => a * Real.sin θ * Q p) := by fun_prop
  have hD2b : ∀ p, ‖a * Real.sin θ * Q p‖ ≤ ‖a‖ * C ^ 2 := by
    intro p
    calc
      _ = ‖a‖ * ‖Real.sin θ‖ * ‖Q p‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖a‖ * 1 * C ^ 2 := by gcongr; first | exact hsin | exact hQb p
      _ = _ := by ring
  have hD1 : ∀ p, HasDerivAt (fun z => F (z, p.2)) (a * P p + a * Real.cos θ * Q p) p.1 := by
    intro p
    have hfirst := (hd (h + a * p.1)).comp p.1
      (((hasDerivAt_id p.1).const_mul a).const_add h)
    have hsecond := (hdd (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))).comp p.1
      (((((hasDerivAt_id p.1).const_mul (Real.cos θ)).add_const (Real.sin θ * p.2)).const_mul a).const_add h)
    convert hfirst.mul hsecond using 1
    · rfl
    · dsimp [P, Q]
      ring
  have hD2 : ∀ p, HasDerivAt (fun w => F (p.1, w)) (a * Real.sin θ * Q p) p.2 := by
    intro p
    have hinner := (((((hasDerivAt_id p.2).const_mul (Real.sin θ)).const_add
      (Real.cos θ * p.1)).const_mul a).const_add h)
    have hsecond := (hdd (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))).comp p.2 hinner
    convert hsecond.const_mul (f (h + a * p.1)) using 1
    · rfl
    · dsimp [Q]
      ring
  have hS1 := gaussian_pair_stein_fst F (fun p => a * P p + a * Real.cos θ * Q p)
    (C ^ 2) (2 * ‖a‖ * C ^ 2) hFc hD1c hD1 hFb hD1b
  have hS2 := gaussian_pair_stein_snd F (fun p => a * Real.sin θ * Q p)
    (C ^ 2) (‖a‖ * C ^ 2) hFc hD2c hD2 hFb hD2b
  rw [integral_add (hIP.const_mul a) (hIQ.const_mul (a * Real.cos θ)),
    integral_const_mul, integral_const_mul] at hS1
  rw [integral_const_mul] at hS2
  have hraw := hasDerivAt_gaussianRotationCovariance_raw f df h a θ C hf hdf hC hd hb hdb
  have heq : (∫ p, f (h + a * p.1) * df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) *
      a * (-Real.sin θ * p.1 + Real.cos θ * p.2) ∂standardGaussianPair) =
      -a ^ 2 * Real.sin θ * ∫ p, P p ∂standardGaussianPair := by
    calc
      _ = ∫ p, (-a * Real.sin θ) * (p.1 * F p) +
          (a * Real.cos θ) * (p.2 * F p) ∂standardGaussianPair := by
        apply integral_congr_ae
        filter_upwards [] with p
        dsimp [F]
        ring
      _ = (-a * Real.sin θ) * (∫ p, p.1 * F p ∂standardGaussianPair) +
          (a * Real.cos θ) * (∫ p, p.2 * F p ∂standardGaussianPair) := by
        rw [integral_add (hcoord.1.const_mul _) (hcoord.2.const_mul _),
          integral_const_mul, integral_const_mul]
      _ = _ := by rw [hS1, hS2]; ring
  rw [heq] at hraw
  exact hraw

lemma gaussian_pair_rotated_integral (f : ℝ → ℝ) (h a θ C : ℝ)
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) (ha : 0 ≤ a) :
    (∫ p, f (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) ∂standardGaussianPair) =
      gaussianExpectation (fun z => f (h + a * z)) := by
  have heq : (fun p : ℝ × ℝ => f (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))) =
      (fun p => f (h + a * Real.cos θ * p.1 + a * Real.sin θ * p.2)) := by
    funext p
    congr 1
    ring
  have hi := integrable_gaussian_pair_bounded
    (fun p : ℝ × ℝ => f (h + a * Real.cos θ * p.1 + a * Real.sin θ * p.2))
    C (by fun_prop) (fun p => hb _)
  rw [heq]
  simp only [standardGaussianPair]
  rw [integral_prod _ hi]
  have hr := gaussian_rotation_expectation h a θ f hf.measurable C hb
  rw [abs_of_nonneg ha] at hr
  exact hr

                                                                                   
                                                                        
                                                                             
                                                                               
                                                                                      
                                          
           
                                                                               
                                              
                                                                                  
                                              
                                                                             
                                          
                                              
                                                                                            
                                                                          
                                                                        
                            
                                            
                                                           
                                 
                                                
                                                                   
                                                             
                                    
                            
                              
                                                                               
                      
                          
          

                                                                            
                                                                                
                                                                   
                             
                                                                     
                                                                          
                                                                             
                                                      
                                                        
                                                                       
                                                            
                                                                                       
                                 
                                                        
                                                                                          
                                                                       
                                       
                                                                                      
        
                                                                                            
                                                             
                                                                      
                                                                      
                
                             
                        
                                                                                                         
                                                      
                                                                                           
                                                                                                       
                                                                                            
                               
                                                   
                                                            
                                                                                      
                                        
                                                                                          
                                                                                                     
                       
                                    
                           
                              
                                                                
                                                            
                                                                                    
                                  
                                    
                                                                                    
                                   
        
                 
                                                              
                 
          

                                                                               
                                                       
                                                              
                                                                
                                                                         
                                                                         
                                                                   
                                                             
                                                                                          
                                      
                                                                                              
                                                                                                      
                            
                                                

end Paper


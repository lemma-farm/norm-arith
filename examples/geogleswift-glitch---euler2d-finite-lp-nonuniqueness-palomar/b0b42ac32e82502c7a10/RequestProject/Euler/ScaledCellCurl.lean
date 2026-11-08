module

public import RequestProject.Euler.CellCurl
public import RequestProject.Euler.ScaledRadialSobolev
public import Mathlib
/-!
# The exact curl of the physical circular datum series

The actual scaled blocks have their prescribed scaled two-interface
vorticities. The infinite velocity and vorticity series retain this
identity under their strong Lebesgue-space limits.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace Euler2D

def scaledCellW (A r : ℝ) (x : R2) : ℝ :=
  A * cellW (r⁻¹ • (x - torusCenter))

def scaledApproxCellCurl (A r : ℝ) (n : ℕ) (x : R2) : ℝ :=
  pd 0 (scaledRadialAverage A r (radialApproxScale n)) x 1 -
    pd 1 (scaledRadialAverage A r (radialApproxScale n)) x 0

lemma scaledApproxCellCurl_eq {r : ℝ} (hr : 0 < r) (A : ℝ) (n : ℕ) (x : R2) :
    scaledApproxCellCurl A r n x =
      A * (2 * profileAverage cellOmegaSq (radialApproxScale n)
        (‖r⁻¹ • (x - torusCenter)‖ ^ 2) +
        2 * ‖r⁻¹ • (x - torusCenter)‖ ^ 2 *
          deriv (profileAverage cellOmegaSq (radialApproxScale n))
            (‖r⁻¹ • (x - torusCenter)‖ ^ 2)) := by
  unfold scaledApproxCellCurl
  rw [pd_scaledRadialAverage hr, pd_scaledRadialAverage hr]
  change A * pd 0 (radialVelocity _ 0) _ 1 - A * pd 1 (radialVelocity _ 0) _ 0 = _
  rw [← mul_sub, radialVelocity_curl
    ((contDiff_profileAverage continuous_cellOmegaSq _).differentiable one_ne_zero)]
  simp only [sub_zero]

lemma ae_scaled_sq_radius_ne_interfaces {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂μT, ‖r⁻¹ • (x - torusCenter)‖ ^ 2 ≠ (3 / 5 : ℝ) ∧
      ‖r⁻¹ • (x - torusCenter)‖ ^ 2 ≠ 1 := by
  have ha : ∀ᵐ x ∂volume, x ∉ sphere torusCenter (r * cellA) :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume torusCenter (r * cellA))
  have h1 : ∀ᵐ x ∂volume, x ∉ sphere torusCenter r :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume torusCenter r)
  filter_upwards [ae_restrict_of_ae ha, ae_restrict_of_ae h1] with x hxa hx1
  have hn := norm_nonneg (r⁻¹ • (x - torusCenter))
  have hscale : ‖r⁻¹ • (x - torusCenter)‖ = r⁻¹ * ‖x - torusCenter‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hna : ‖x - torusCenter‖ ≠ r * cellA := by
    simpa only [mem_sphere_iff_norm] using hxa
  have hn1 : ‖x - torusCenter‖ ≠ r := by
    simpa only [mem_sphere_iff_norm] using hx1
  constructor
  · intro he
    have he' : ‖r⁻¹ • (x - torusCenter)‖ = cellA := by
      nlinarith [cellA_sq, cellA_pos]
    rw [hscale] at he'
    have hm := congrArg (fun z : ℝ => r * z) he'
    change r * (r⁻¹ * ‖x - torusCenter‖) = r * cellA at hm
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hm
    exact hna hm
  · intro he
    have he' : ‖r⁻¹ • (x - torusCenter)‖ = 1 := by nlinarith
    rw [hscale] at he'
    have hm := congrArg (fun z : ℝ => r * z) he'
    change r * (r⁻¹ * ‖x - torusCenter‖) = r * 1 at hm
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_one] at hm
    exact hn1 hm

lemma tendsto_scaledApproxCellCurl_ae {r : ℝ} (hr : 0 < r) (A : ℝ) :
    ∀ᵐ x ∂μT, Tendsto (fun n => scaledApproxCellCurl A r n x) atTop
      (𝓝 (scaledCellW A r x)) := by
  filter_upwards [ae_scaled_sq_radius_ne_interfaces hr] with x hx
  have hd := tendsto_deriv_profileAverage_of_hasDerivAt continuous_cellOmegaSq
    (hasDerivAt_cellOmegaSq hx.1 hx.2)
  have hv := (tendsto_profileAverage continuous_cellOmegaSq
    (‖r⁻¹ • (x - torusCenter)‖ ^ 2)).const_mul 2
  have hlim := (hv.add (hd.const_mul (2 * ‖r⁻¹ • (x - torusCenter)‖ ^ 2))).const_mul A
  simpa only [scaledApproxCellCurl_eq hr, cellOmegaSq_curl_identity,
    scaledCellW, cellW_eq_cellCurlProfile] using hlim

lemma continuous_scaledApproxCellCurl (A r : ℝ) (n : ℕ) :
    Continuous (scaledApproxCellCurl A r n) := by
  exact ((EuclideanSpace.proj 1 : R2 →L[ℝ] ℝ).continuous.comp
    (continuous_pd_of_contDiff_one _ (contDiff_scaledRadialAverage A r _) 0)).sub
      ((EuclideanSpace.proj 0 : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one _ (contDiff_scaledRadialAverage A r _) 1))

lemma norm_scaledApproxCellCurl_le {r : ℝ} (hr : 0 < r) (A : ℝ) (n : ℕ) (x : R2) :
    ‖scaledApproxCellCurl A r n x‖ ≤ 14 * |A| := by
  have h0 := (abs_coord_le (pd 0 (scaledRadialAverage A r (radialApproxScale n)) x) 1).trans
    (norm_pd_scaledRadialAverage_le (radialApproxScale_pos n) hr A x 0)
  have h1 := (abs_coord_le (pd 1 (scaledRadialAverage A r (radialApproxScale n)) x) 0).trans
    (norm_pd_scaledRadialAverage_le (radialApproxScale_pos n) hr A x 1)
  exact (norm_sub_le _ _).trans (by
    simpa only [Real.norm_eq_abs] using (show
      |pd 0 (scaledRadialAverage A r (radialApproxScale n)) x 1| +
        |pd 1 (scaledRadialAverage A r (radialApproxScale n)) x 0| ≤ 14 * |A| by linarith))

                                                                                       
                                                                           
                                                                                                 
                                                                              
                                                                                 

                                                                        
                                      
                                                                                
                                                          
                                                                                         
           
                                                                               
                                                                 
           
                                           
                   
                                                                                               
                                                                   
                            

                                                                         
                                                                           
                                                                                        
                                                               
                                                                                     
                                                            
            
                                               
                                                                 
                         
                                                              
                                                                                     
                                                                             
                                            
                                                              
                                            
                       
                                                                               
                                                                      
                    
                                                                               
                                     
                                                                    

                                                                        
                                                                                      
                                
                                                                    
                                 
                                                                       
                                           
                                                                            

                                                                            
                                        
                                                              
                                                          
                                                                                    
                                                           

end Euler2D

end

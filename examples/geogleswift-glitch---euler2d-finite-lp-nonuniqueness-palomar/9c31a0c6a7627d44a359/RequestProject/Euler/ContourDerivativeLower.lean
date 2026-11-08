module

public import RequestProject.Euler.ContourCauchyPrincipalValue

/-! A genuine short-chord lower bound passes to the actual derivative
through its secant limit. This justifies subsequent divisions by the
contour derivative. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem norm_hasDerivAt_lower_of_chord {z : ℝ → ℂ} {dz : ℂ} {θ c r : ℝ}
    (hz : HasDerivAt z dz θ) (hr : 0 < r)
    (hchord : ∀ τ : ℝ, |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    c ≤ ‖dz‖ := by
  have hlim := hz.tendsto_slope_zero.norm
  have hnb : Ioo (-r) r ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hr
  have hev : ∀ᶠ τ : ℝ in 𝓝[≠] 0,
      c ≤ ‖τ⁻¹ • (z (θ + τ) - z θ)‖ := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hnb] with τ hτ hI
    have ht : τ ≠ 0 := hτ
    have htpos : 0 < |τ| := abs_pos.mpr ht
    have hb := hchord τ (abs_le.mpr ⟨hI.1.le, hI.2.le⟩)
    rw [norm_smul, Real.norm_eq_abs, abs_inv, inv_mul_eq_div]
    apply (le_div_iff₀ htpos).mpr
    simpa only [norm_sub_rev] using hb
  exact isClosed_Ici.mem_of_tendsto hlim hev

                                                                                
                                                  
                                                                              
                                              
                                                                                                 
                          

                                                                             
                
                                                  
                                                                              
                                            
                                                                            

end Euler2D

end

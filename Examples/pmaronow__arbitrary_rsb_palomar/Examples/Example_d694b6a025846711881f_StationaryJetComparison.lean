module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.vb64f7a47fb49.DepthPaper.ImplicitStationaryJets
set_option autoImplicit false
set_option backward.privateInPublic true
@[expose] public section
/-! Quantitative comparison of the genuine first two stationary jets.  The
input errors concern the actual Jacobians of the two gradient maps at their
selected graph points. Scalar-potential errors and a fixed fourth-jet bound
can supply these errors by a mean-value estimate. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
variable {Θ E : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 64
private theorem tangent_norm_le {q : Θ→E} {θ : Θ} {A : ℝ}
    (hA : 1≤A) (hD : ‖fderiv ℝ q θ‖ ≤ A) {v : Θ} (hv : ‖v‖=1) :
    ‖(v,fderiv ℝ q θ v)‖ ≤ A := by
  rw [Prod.norm_def,hv]
  apply max_le hA
  exact ((fderiv ℝ q θ).le_opNorm v).trans (by simpa only [hv,mul_one] using hD)
private theorem tangent_difference_norm_le {q r : Θ→E} {θ : Θ} {D : ℝ}
    (hD : ‖fderiv ℝ q θ-fderiv ℝ r θ‖ ≤ D) {v : Θ} (hv : ‖v‖=1) :
    ‖(v,fderiv ℝ q θ v)-(v,fderiv ℝ r θ v)‖ ≤ D := by
  have he : (v,fderiv ℝ q θ v)-(v,fderiv ℝ r θ v)=
      (0,(fderiv ℝ q θ-fderiv ℝ r θ) v) := by ext <;> simp
  rw [he,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
  exact ((fderiv ℝ q θ-fderiv ℝ r θ).le_opNorm v).trans
    (by simpa only [hv,mul_one] using hD)
/-- Comparison of the true first derivatives; no implicit derivative formula
is supplied as an assumption. -/
theorem stationary_first_comparison
    {F G : Θ×E→E→L[ℝ]ℝ} {q r : Θ→E} {θ : Θ} {κ D η : ℝ}
    (hF : ContDiffAt ℝ ∞ F (stationaryGraph q θ))
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph r θ))
    (hq : ContDiffAt ℝ ∞ q θ) (hr : ContDiffAt ℝ ∞ r θ)
    (heq : ∀ᶠu in 𝓝 θ,F (stationaryGraph q u)=0)
    (her : ∀ᶠu in 𝓝 θ,G (stationaryGraph r u)=0)
    (hκ : 0<κ) (hD : 0≤D) (hη : 0≤η)
    (hBF : ∀z:E,κ*‖z‖^2 ≤ fderiv ℝ F (stationaryGraph q θ) (0,z) z)
    (hBG : ∀z:E,κ*‖z‖^2 ≤ fderiv ℝ G (stationaryGraph r θ) (0,z) z)
    (hG1 : ‖fderiv ℝ G (stationaryGraph r θ)‖ ≤ D)
    (hdiff : ‖fderiv ℝ F (stationaryGraph q θ)-fderiv ℝ G (stationaryGraph r θ)‖ ≤ η) :
    ‖fderiv ℝ q θ-fderiv ℝ r θ‖ ≤ η*max 1 (D/κ)/κ := by
  let L := fderiv ℝ F (stationaryGraph q θ)
  let M := fderiv ℝ G (stationaryGraph r θ)
  let A := max 1 (D/κ)
  have hA : 0≤A := (show (0:ℝ)≤1 by norm_num).trans (le_max_left _ _)
  have hr1 := (stationary_first_norm_bound hG hr her hκ hBG).trans
    (div_le_div_of_nonneg_right hG1 hκ.le)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hf0 : L (v,fderiv ℝ q θ v)=0 := by
    have hh := stationary_first_equation hF hq heq v
    have hid : (v,fderiv ℝ q θ v)=(v,0)+(0,fderiv ℝ q θ v) := by simp
    rw [hid,map_add,hh,add_neg_cancel]
  have hg0 : M (v,fderiv ℝ r θ v)=0 := by
    have hh := stationary_first_equation hG hr her v
    have hid : (v,fderiv ℝ r θ v)=(v,0)+(0,fderiv ℝ r θ v) := by simp
    rw [hid,map_add,hh,add_neg_cancel]
  have he : L (0,(fderiv ℝ q θ-fderiv ℝ r θ) v)=
      -(L-M) (v,fderiv ℝ r θ v) := by
    have hvv : (0,(fderiv ℝ q θ-fderiv ℝ r θ) v)=
        (v,fderiv ℝ q θ v)-(v,fderiv ℝ r θ v) := by ext <;> simp
    rw [hvv,map_sub,hf0,sub_apply,hg0,sub_zero,zero_sub]
  have hc := coercive_linear_vector_bound (L.comp (ContinuousLinearMap.inr ℝ Θ E))
    hκ hBF ((fderiv ℝ q θ-fderiv ℝ r θ) v)
  change ‖(fderiv ℝ q θ-fderiv ℝ r θ) v‖ ≤
    ‖L (0,(fderiv ℝ q θ-fderiv ℝ r θ) v)‖/κ at hc
  rw [he,norm_neg] at hc
  have ht := tangent_norm_le (le_max_left 1 (D/κ)) (hr1.trans (le_max_right _ _)) hv
  apply hc.trans
  apply div_le_div_of_nonneg_right _ hκ.le
  exact ((L-M).le_opNorm _).trans (mul_le_mul hdiff ht (norm_nonneg _) hη)
end DepthPaper

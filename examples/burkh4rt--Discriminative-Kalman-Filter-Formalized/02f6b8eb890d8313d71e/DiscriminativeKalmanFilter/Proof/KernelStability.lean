module
public import DiscriminativeKalmanFilter.Proof.KernelMass
public import DiscriminativeKalmanFilter.Proof.NormalizeConvergence

@[expose] public section

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
variable {d : ℕ}

theorem kernelProduct_distance_le (M : Model d) {s s' u u' : Density d}
    (hs : IsPDF s) (hs' : IsPDF s') (hu : IsPDF u) (hu' : IsPDF u') :
    (l1Distance (fun z => u z * predictDensity M s z)
      (fun z => u' z * predictDensity M s' z)).toReal ≤
    gaussianPDF 0 M.Γ 0 * (l1Distance u u').toReal +
      gaussianPDF 0 M.Γ 0 * (l1Distance s s').toReal := by
  let β := gaussianPDF 0 M.Γ 0
  let δ := (l1Distance s s').toReal
  have hδ : 0 ≤ δ := ENNReal.toReal_nonneg
  have hβ : 0 ≤ β := (gaussianPDF_pos 0 M.Γ_posDef 0).le
  rw [l1Distance_toReal (kernelProduct_integrable M hs hu) (kernelProduct_integrable M hs' hu')]
  have hi1 := (hu.2.1.sub hu'.2.1).norm.const_mul β
  have hi2 := hu'.2.1.norm.const_mul (β * δ)
  calc
    _ ≤ ∫ z, β * ‖u z - u' z‖ + (β * δ) * ‖u' z‖ ∂volume := by
      apply integral_mono_ae
        ((kernelProduct_integrable M hs hu).sub (kernelProduct_integrable M hs' hu')).norm
        (hi1.add hi2)
      filter_upwards [] with z
      simp only [Pi.sub_apply]
      have he : u z * predictDensity M s z - u' z * predictDensity M s' z =
        (u z - u' z) * predictDensity M s z +
          u' z * (predictDensity M s z - predictDensity M s' z) := by ring
      rw [he]
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_mul]
      have hp : ‖predictDensity M s z‖ ≤ β := by
        simpa only [l1Norm_toReal_pdf hs, mul_one] using predict_norm_le M hs.2.1 z
      have hdiff := predict_difference_le M hs.2.1 hs'.2.1 z
      calc
        _ ≤ ‖u z - u' z‖ * β + ‖u' z‖ * (β * δ) := by gcongr
        _ = _ := by simp only [Pi.add_apply]; ring
    _ = β * (l1Distance u u').toReal + β * δ := by
      have hadd := integral_add hi1 hi2
      simp only [Pi.sub_apply] at hadd
      rw [hadd, integral_const_mul, integral_const_mul,
        ← l1Distance_toReal hu.2.1 hu'.2.1, ← l1Norm_toReal hu'.2.1.1,
        l1Norm_toReal_pdf hu', mul_one]

theorem kernelProduct_normalized_tendsto (M : Model d)
    {s s' u u' : ℕ+ → Density d}
    (hs : ∀ n, IsPDF (s n)) (hs' : ∀ n, IsPDF (s' n))
    (hu : ∀ n, IsPDF (u n)) (hu' : ∀ n, IsPDF (u' n))
    (P : ProbabilityMeasure (State d)) (b : State d)
    (hws : Weakly s P) (hws' : Weakly s' P)
    (hwu : Weakly u (Measure.dirac b)) (hwu' : Weakly u' (Measure.dirac b))
    (hds : Tendsto (fun n => l1Distance (s n) (s' n)) atTop (𝓝 0))
    (hdu : Tendsto (fun n => l1Distance (u n) (u' n)) atTop (𝓝 0)) :
    Tendsto (fun n => (l1Distance
      (fun z => u n z * predictDensity M (s n) z /
        (∫ y, u n y * predictDensity M (s n) y ∂volume))
      (fun z => u' n z * predictDensity M (s' n) z /
        (∫ y, u' n y * predictDensity M (s' n) y ∂volume))).toReal) atTop (𝓝 0) := by
  apply normalized_l1_tendsto
    (fun n => kernelProduct_integrable M (hs n) (hu n))
    (fun n => kernelProduct_integrable M (hs' n) (hu' n))
    (fun n => ?_) (kernel_limit_pos M P b)
    (kernelProduct_mass_tendsto M hs hu P b hws hwu)
    (kernelProduct_mass_tendsto M hs' hu' P b hws' hwu')
  · have hsr := (l1Distance_zero_tendsto_iff (fun n => (hs n).2.1) (fun n => (hs' n).2.1)).mp hds
    have hur := (l1Distance_zero_tendsto_iff (fun n => (hu n).2.1) (fun n => (hu' n).2.1)).mp hdu
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
      (fun n => kernelProduct_distance_le M (hs n) (hs' n) (hu n) (hu' n))
    simpa using (hur.const_mul (gaussianPDF 0 M.Γ 0)).add (hsr.const_mul (gaussianPDF 0 M.Γ 0))
  · filter_upwards [(hu' n).1] with z hz
    exact mul_nonneg hz (predict_nonneg M (hs' n).1 z)

end DiscriminativeKalmanFilter.Proof

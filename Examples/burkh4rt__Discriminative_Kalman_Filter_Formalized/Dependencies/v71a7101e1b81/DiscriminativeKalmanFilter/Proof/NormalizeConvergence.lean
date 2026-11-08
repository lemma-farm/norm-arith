module
public import Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Proof.L1Tools
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
variable {d : ℕ}
theorem normalized_distance_le {f g : Density d}
    (hf : Integrable f volume) (hg : Integrable g volume) (a b : ℝ) :
    (l1Distance (fun z => f z / a) (fun z => g z / b)).toReal ≤
      |a⁻¹| * (l1Distance f g).toReal + |a⁻¹ - b⁻¹| * (l1Norm g).toReal := by
  rw [l1Distance_toReal (hf.div_const _) (hg.div_const _), l1Distance_toReal hf hg,
    l1Norm_toReal hg.1, ← integral_const_mul, ← integral_const_mul]
  have h1 := (hf.sub hg).norm.const_mul |a⁻¹|
  have h2 := hg.norm.const_mul |a⁻¹ - b⁻¹|
  have ha := integral_add h1 h2
  simp only [Pi.sub_apply] at ha
  rw [← ha]
  apply integral_mono ((hf.div_const _).sub (hg.div_const _)).norm (h1.add h2)
  intro z
  simp only [Pi.sub_apply, Pi.add_apply]
  have he : f z / a - g z / b = a⁻¹ * (f z - g z) + (a⁻¹ - b⁻¹) * g z := by
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul]; rfl)
theorem normalized_l1_tendsto {f g : ℕ+ → Density d}
    (hf : ∀ n, Integrable (f n) volume) (hg : ∀ n, Integrable (g n) volume)
    (hgn : ∀ n, ∀ᵐ z ∂volume, 0 ≤ g n z)
    {a : ℝ} (ha : 0 < a)
    (hmf : Tendsto (fun n => ∫ z, f n z ∂volume) atTop (𝓝 a))
    (hmg : Tendsto (fun n => ∫ z, g n z ∂volume) atTop (𝓝 a))
    (hd : Tendsto (fun n => (l1Distance (f n) (g n)).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (l1Distance
      (fun z => f n z / (∫ y, f n y ∂volume))
      (fun z => g n z / (∫ y, g n y ∂volume))).toReal) atTop (𝓝 0) := by
  have hnorm n : (l1Norm (g n)).toReal = ∫ z, g n z ∂volume := by
    rw [l1Norm_eq_integral (hg n) (hgn n), ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae (hgn n)
  have hb := ((hmf.inv₀ ha.ne').abs.mul hd).add
    (((hmf.inv₀ ha.ne').sub (hmg.inv₀ ha.ne')).abs.mul hmg)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => (normalized_distance_le (hf n) (hg n) _ _).trans_eq ?_)
    (by simpa using hb)
  rw [hnorm]
  simp only [abs_inv]
end DiscriminativeKalmanFilter.Proof

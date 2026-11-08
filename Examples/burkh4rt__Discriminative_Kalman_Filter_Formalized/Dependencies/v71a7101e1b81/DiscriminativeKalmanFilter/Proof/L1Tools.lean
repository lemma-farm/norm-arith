module
public import Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Proof.Normalization
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
variable {d : ℕ}
theorem l1Norm_finite {f : Density d} (hf : Integrable f volume) : l1Norm f < ⊤ := by
  have h := hf.2
  rw [hasFiniteIntegral_iff_norm] at h
  exact h
theorem l1Distance_finite {f g : Density d}
    (hf : Integrable f volume) (hg : Integrable g volume) : l1Distance f g < ⊤ :=
  l1Norm_finite (hf.sub hg)
theorem l1Distance_toReal {f g : Density d}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (l1Distance f g).toReal = ∫ z, ‖f z - g z‖ ∂volume :=
  l1Norm_toReal (hf.sub hg).1
theorem l1Distance_comm (f g : Density d) : l1Distance f g = l1Distance g f := by
  unfold l1Distance l1Norm
  apply lintegral_congr
  intro z
  simp only [Pi.sub_apply, abs_sub_comm]
theorem l1Distance_triangle {f g h : Density d}
    (hf : Integrable f volume) (hg : Integrable g volume) (hh : Integrable h volume) :
    (l1Distance f h).toReal ≤ (l1Distance f g).toReal + (l1Distance g h).toReal := by
  rw [l1Distance_toReal hf hh, l1Distance_toReal hf hg, l1Distance_toReal hg hh]
  have hadd := integral_add (hf.sub hg).norm (hg.sub hh).norm
  simp only [Pi.sub_apply] at hadd
  rw [← hadd]
  apply integral_mono (hf.sub hh).norm ((hf.sub hg).norm.add (hg.sub hh).norm)
  intro z
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _
theorem l1Distance_zero_tendsto_iff {f g : ℕ+ → Density d}
    (hf : ∀ n, Integrable (f n) volume) (hg : ∀ n, Integrable (g n) volume) :
    Tendsto (fun n => l1Distance (f n) (g n)) atTop (𝓝 0) ↔
    Tendsto (fun n => (l1Distance (f n) (g n)).toReal) atTop (𝓝 0) := by
  exact (ENNReal.tendsto_toReal_zero_iff (fun n => (l1Distance_finite (hf n) (hg n)).ne)).symm
end DiscriminativeKalmanFilter.Proof

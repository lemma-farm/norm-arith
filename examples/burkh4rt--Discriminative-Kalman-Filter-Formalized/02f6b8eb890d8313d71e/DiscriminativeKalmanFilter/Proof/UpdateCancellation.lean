module
public import DiscriminativeKalmanFilter.Proof.KernelStability
public import DiscriminativeKalmanFilter.Proof.Reweighting
public import DiscriminativeKalmanFilter.Proof.C1C2

@[expose] public section

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
variable {d : ℕ}

theorem update_times_prior (M : Model d) (s u : Density d) (z : State d) :
    updateDensity M s u z * prior M z =
      (u z * predictDensity M s z) / (l1Norm (updateWeight M s u)).toReal := by
  have hp : prior M z ≠ 0 := (gaussianPDF_pos 0 M.S_posDef z).ne'
  unfold updateDensity updateWeight
  field_simp

theorem normalized_update_times_prior (M : Model d) {s u : Density d}
    (hd : UpdateDefined M s u) :
    (fun z => updateDensity M s u z * prior M z /
      (∫ y, updateDensity M s u y * prior M y ∂volume)) =
    fun z => (u z * predictDensity M s z) / (∫ y, u y * predictDensity M s y ∂volume) := by
  have hn : (l1Norm (updateWeight M s u)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hd.2.1.ne' hd.2.2.ne).ne'
  funext z
  simp_rw [update_times_prior]
  rw [integral_div]
  exact div_div_div_cancel_right₀ hn _ _

theorem weakly_eventuallyEq {f g : ℕ+ → Density d} {P : Measure (State d)}
    (he : ∀ᶠ n in atTop, f n = g n) (hw : Weakly f P) : Weakly g P := by
  intro F
  apply (hw F).congr'
  filter_upwards [he] with n hn
  rw [hn]

end DiscriminativeKalmanFilter.Proof

module
public import DiscriminativeKalmanFilter.Proof.GaussianBasics
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DiscriminativeKalmanFilter.Proof

variable {d : ℕ}

theorem predict_integrable (M : Model d) {s : Density d} (hs : Integrable s volume)
    (z : State d) : Integrable (fun y => transition M y z * s y) volume := by
  apply hs.bdd_mul
  · exact (transition_continuous M |>.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_pos (transition_pos M y z)]
    exact transition_le M y z

theorem predict_nonneg (M : Model d) {s : Density d}
    (hs : ∀ᵐ y ∂volume, 0 ≤ s y) (z : State d) : 0 ≤ predictDensity M s z := by
  apply integral_nonneg_of_ae
  filter_upwards [hs] with y hy using mul_nonneg (transition_pos M y z).le hy

theorem predict_norm_le (M : Model d) {s : Density d} (hs : Integrable s volume)
    (z : State d) : ‖predictDensity M s z‖ ≤ gaussianPDF 0 M.Γ 0 * (l1Norm s).toReal := by
  calc
    _ ≤ ∫ y, gaussianPDF 0 M.Γ 0 * ‖s y‖ ∂volume := by
      apply norm_integral_le_of_norm_le (hs.norm.const_mul _)
      filter_upwards [] with y
      rw [norm_mul, Real.norm_eq_abs (transition M y z), abs_of_pos (transition_pos M y z)]
      exact mul_le_mul_of_nonneg_right (transition_le M y z) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, l1Norm_toReal hs.1]

theorem predict_sub (M : Model d) {s s' : Density d}
    (hs : Integrable s volume) (hs' : Integrable s' volume) :
    predictDensity M (s - s') = predictDensity M s - predictDensity M s' := by
  funext z
  simp only [predictDensity, Pi.sub_apply, mul_sub]
  exact integral_sub (predict_integrable M hs z) (predict_integrable M hs' z)

theorem predict_difference_le (M : Model d) {s s' : Density d}
    (hs : Integrable s volume) (hs' : Integrable s' volume) (z : State d) :
    ‖predictDensity M s z - predictDensity M s' z‖ ≤
      gaussianPDF 0 M.Γ 0 * (l1Distance s s').toReal := by
  simpa only [predict_sub M hs hs', Pi.sub_apply, l1Distance] using
    predict_norm_le M (hs.sub hs') z

theorem predict_continuous (M : Model d) {s : Density d} (hs : Integrable s volume) :
    Continuous (predictDensity M s) := by
  apply continuous_of_dominated
    (bound := fun y => gaussianPDF 0 M.Γ 0 * ‖s y‖)
  · intro z
    exact (predict_integrable M hs z).1
  · intro z
    filter_upwards [] with y
    rw [norm_mul, Real.norm_eq_abs (transition M y z), abs_of_pos (transition_pos M y z)]
    exact mul_le_mul_of_nonneg_right (transition_le M y z) (norm_nonneg _)
  · exact hs.norm.const_mul _
  · filter_upwards [] with y
    exact ((gaussianPDF_continuous (M.A *ᵥ y) M.Γ).mul continuous_const)

theorem l1Norm_toReal_pdf {s : Density d} (hs : IsPDF s) : (l1Norm s).toReal = 1 := by
  rw [l1Norm_toReal hs.2.1.1]
  calc
    (∫ y, ‖s y‖ ∂volume) = ∫ y, s y ∂volume := by
      apply integral_congr_ae
      filter_upwards [hs.1] with y hy using Real.norm_of_nonneg hy
    _ = 1 := hs.2.2

theorem updateWeight_nonneg (M : Model d) {s u : Density d}
    (hs : IsPDF s) (hu : IsPDF u) : ∀ᵐ z ∂volume, 0 ≤ updateWeight M s u z := by
  filter_upwards [hu.1] with z hz
  exact div_nonneg (mul_nonneg hz (predict_nonneg M hs.1 z))
    (gaussianPDF_pos 0 M.S_posDef z).le

theorem normalized_isPDF {f : Density d}
    (hf : AEStronglyMeasurable f volume) (hn : ∀ᵐ z ∂volume, 0 ≤ f z)
    (hp : 0 < l1Norm f) (hfin : l1Norm f < ⊤) :
    IsPDF (fun z => f z / (l1Norm f).toReal) := by
  have hreal : 0 < (l1Norm f).toReal := ENNReal.toReal_pos hp.ne' hfin.ne
  have hi : Integrable f volume := by
    refine ⟨hf, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact hfin
  have he : ∫ z, f z ∂volume = (l1Norm f).toReal := by
    rw [l1Norm_toReal hf]
    apply integral_congr_ae
    filter_upwards [hn] with z hz using (Real.norm_of_nonneg hz).symm
  refine ⟨?_, hi.div_const _, ?_⟩
  · filter_upwards [hn] with z hz using div_nonneg hz hreal.le
  · rw [integral_div, he, div_self hreal.ne']

theorem updateDensity_isPDF (M : Model d) {s u : Density d}
    (hs : IsPDF s) (hu : IsPDF u) (hd : UpdateDefined M s u) :
    IsPDF (updateDensity M s u) :=
  normalized_isPDF hd.1 (updateWeight_nonneg M hs hu) hd.2.1 hd.2.2

end DiscriminativeKalmanFilter.Proof

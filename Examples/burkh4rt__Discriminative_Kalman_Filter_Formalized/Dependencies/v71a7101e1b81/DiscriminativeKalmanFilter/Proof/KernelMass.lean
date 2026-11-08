module
public import Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Proof.L1Tools
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
variable {d : ℕ}
def transitionBCF (M : Model d) : BoundedContinuousFunction (State d × State d) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun yz => transition M yz.1 yz.2)
    (transition_continuous M) (gaussianPDF 0 M.Γ 0) (fun yz => by
      rw [Real.norm_eq_abs, abs_of_pos (transition_pos M yz.1 yz.2)]
      exact transition_le M yz.1 yz.2)
theorem kernelProduct_integrable (M : Model d) {s u : Density d}
    (hs : IsPDF s) (hu : IsPDF u) :
    Integrable (fun z => u z * predictDensity M s z) volume := by
  apply hu.2.1.mul_bdd (predict_continuous M hs.2.1).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [l1Norm_toReal_pdf hs, mul_one] using predict_norm_le M hs.2.1 z
theorem kernelProduct_integral (M : Model d) {s u : Density d}
    (hs : IsPDF s) (hu : IsPDF u) :
    (∫ z, u z * predictDensity M s z ∂volume) =
      ∫ yz, transition M yz.1 yz.2 ∂(densityMeasure s).prod (densityMeasure u) := by
  let :=  isProbabilityMeasure_densityMeasure hs
  let :=  isProbabilityMeasure_densityMeasure hu
  have hj := (transitionBCF M).integrable ((densityMeasure s).prod (densityMeasure u))
  change Integrable (fun yz : State d × State d => transition M yz.1 yz.2)
    ((densityMeasure s).prod (densityMeasure u)) at hj
  rw [integral_prod _ hj, integral_integral_swap hj]
  rw [integral_densityMeasure hu]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [integral_densityMeasure hs]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y using mul_comm _ _
theorem kernelProduct_mass_tendsto (M : Model d) {s u : ℕ+ → Density d}
    (hs : ∀ n, IsPDF (s n)) (hu : ∀ n, IsPDF (u n))
    (P : ProbabilityMeasure (State d)) (b : State d)
    (hws : Weakly s P) (hwu : Weakly u (Measure.dirac b)) :
    Tendsto (fun n => ∫ z, u n z * predictDensity M (s n) z ∂volume) atTop
      (𝓝 (∫ y, transition M y b ∂P)) := by
  let Q : ProbabilityMeasure (State d) := ⟨Measure.dirac b, inferInstance⟩
  have hS := (weakly_iff_tendsto hs P).mp hws
  have hU := (weakly_iff_tendsto hu Q).mp hwu
  have ht := ProbabilityMeasure.continuous_prod.tendsto (P, Q) |>.comp (hS.prodMk_nhds hU)
  have hw := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht (transitionBCF M)
  have hj := (transitionBCF M).integrable ((P : Measure (State d)).prod (Measure.dirac b))
  change Integrable (fun yz : State d × State d => transition M yz.1 yz.2)
    ((P : Measure (State d)).prod (Measure.dirac b)) at hj
  have hl : (∫ yz, transition M yz.1 yz.2 ∂(P : Measure (State d)).prod (Measure.dirac b)) =
      ∫ y, transition M y b ∂P := by
    rw [integral_prod _ hj]
    simp only [integral_dirac]
  change Tendsto (fun n => ∫ yz, transition M yz.1 yz.2 ∂
    (densityMeasure (s n)).prod (densityMeasure (u n))) atTop
    (𝓝 (∫ yz, transition M yz.1 yz.2 ∂(P : Measure (State d)).prod (Measure.dirac b))) at hw
  simpa only [← kernelProduct_integral M (hs _) (hu _), hl] using hw
theorem kernel_limit_pos (M : Model d) (P : ProbabilityMeasure (State d)) (b : State d) :
    0 < ∫ y, transition M y b ∂P := by
  let g := BoundedContinuousFunction.ofNormedAddCommGroup (fun y => transition M y b)
    ((transition_continuous M).comp (continuous_id.prodMk continuous_const))
    (gaussianPDF 0 M.Γ 0) (fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (transition_pos M y b)]
      exact transition_le M y b)
  rw [integral_pos_iff_support_of_nonneg (fun y => (transition_pos M y b).le) (g.integrable P)]
  have he : Function.support (fun y => transition M y b) = Set.univ := by
    ext y
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (transition_pos M y b).ne'
  rw [he, measure_univ]
  exact zero_lt_one
end DiscriminativeKalmanFilter.Proof

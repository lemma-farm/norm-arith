module
public import Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Proof.L1Tools
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
variable {d : ℕ}
/-- The two outer terms in the five-term decomposition (B.2), on either side. -/
theorem weakly_dirac_reweight {f : ℕ+ → Density d} {b : State d}
    (hf : ∀ n, IsPDF (f n)) (hw : Weakly f (Measure.dirac b))
    (g : BoundedContinuousFunction (State d) ℝ) (hg : ∀ z, 0 ≤ g z)
    (hgb : 0 < g b) :
    Tendsto (fun n => (l1Distance (f n)
      (fun z => f n z * g z / (∫ y, f n y * g y ∂volume))).toReal) atTop (𝓝 0) := by
  let m := fun n => ∫ z, f n z * g z ∂volume
  have hi n := bounded_test_integrable (hf n).2.1 g
  have hm : Tendsto m atTop (𝓝 (g b)) := by
    have ht := hw g
    simp only [integral_dirac] at ht
    simpa only [m, integral_densityMeasure (hf _)] using ht
  let F : BoundedContinuousFunction (State d) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun z => |1 - g z / g b|)
      (by fun_prop) (1 + ‖g‖ / |g b|) (fun z => by
        rw [Real.norm_eq_abs, abs_abs]
        calc
          _ ≤ |(1 : ℝ)| + |g z / g b| := abs_sub _ _
          _ ≤ 1 + ‖g‖ / |g b| := by
            rw [abs_one, abs_div]
            gcongr
            exact g.norm_coe_le_norm z)
  have hF : F b = 0 := by
    change |1 - g b / g b| = 0
    rw [div_self hgb.ne', sub_self, abs_zero]
  have hfirst : Tendsto (fun n => ∫ z, f n z * F z ∂volume) atTop (𝓝 0) := by
    have ht := hw F
    simp only [integral_dirac, hF] at ht
    simpa only [integral_densityMeasure (hf _)] using ht
  have hsecond : Tendsto (fun n => |1 / g b - 1 / m n| * m n) atTop (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x := 1 / g b)).sub
      ((tendsto_const_nhds (x := (1 : ℝ))).div hm hgb.ne')).abs.mul hm
    simpa using ht
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (g := fun n => (∫ z, f n z * F z ∂volume) + |1 / g b - 1 / m n| * m n)
  · intro n
    rw [l1Distance_toReal (hf n).2.1 ((hi n).div_const _)]
    have hnorm : (∫ z, ‖f n z * g z‖ ∂volume) = m n := by
      apply integral_congr_ae
      filter_upwards [(hf n).1] with z hz using Real.norm_of_nonneg (mul_nonneg hz (hg z))
    rw [← hnorm, ← integral_const_mul, ← integral_add (bounded_test_integrable (hf n).2.1 F)
      ((hi n).norm.const_mul _)]
    apply integral_mono_ae ((hf n).2.1.sub ((hi n).div_const _)).norm
      ((bounded_test_integrable (hf n).2.1 F).add ((hi n).norm.const_mul _))
    filter_upwards [(hf n).1] with z hz
    have he : f n z - f n z * g z / m n =
        f n z * (1 - g z / g b) + (1 / g b - 1 / m n) * (f n z * g z) := by
      simp only [div_eq_mul_inv]
      ring
    simp only [Pi.sub_apply, Pi.add_apply, hnorm]
    change ‖f n z - f n z * g z / m n‖ ≤ _
    rw [he]
    calc
      _ ≤ ‖f n z * (1 - g z / g b)‖ + ‖(1 / g b - 1 / m n) * (f n z * g z)‖ := norm_add_le _ _
      _ = _ := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hz]
        rfl
  · simpa using hfirst.add hsecond
end DiscriminativeKalmanFilter.Proof

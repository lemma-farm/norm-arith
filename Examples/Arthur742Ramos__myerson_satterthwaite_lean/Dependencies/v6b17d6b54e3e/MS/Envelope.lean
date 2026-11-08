import Examples.Arthur742Ramos__myerson_satterthwaite_lean.Dependencies.v6b17d6b54e3e.MS.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.Monotone
set_option linter.style.haveILetI false
open MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace MSData
theorem Q_nonneg (D : MSData) (v : ℝ) (hv : v ∈ Set.Icc D.a1 D.b1) : 0 ≤ D.Q v := by
  rw [Q_def, interimQ]
  apply integral_nonneg_of_ae
  filter_upwards [D.nu.support_mem_ae] with c hc
  exact D.q_nonneg v hv c (D.nu_supported hc)
theorem Q_le_one (D : MSData) (v : ℝ) (hv : v ∈ Set.Icc D.a1 D.b1) : D.Q v ≤ 1 := by
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  have hrange : ∀ᵐ c ∂D.nu, D.q (v, c) ∈ Set.Icc 0 1 := by
    filter_upwards [D.nu.support_mem_ae] with c hc
    exact ⟨D.q_nonneg v hv c (D.nu_supported hc), D.q_le_one v hv c (D.nu_supported hc)⟩
  have hqint : Integrable (fun c => D.q (v, c)) D.nu := by
    exact (memLp_of_bounded hrange (D.q_sectionB v hv) 1).integrable (by norm_num)
  have hle := integral_mono_ae hqint (integrable_const (1 : ℝ)) <| by
    filter_upwards [D.nu.support_mem_ae] with c hc
    exact D.q_le_one v hv c (D.nu_supported hc)
  rw [Q_def, interimQ]
  simpa [integral_const] using hle
theorem U_lip (D : MSData) (v : ℝ) (hv : v ∈ Set.Icc D.a1 D.b1)
    (v' : ℝ) (hv' : v' ∈ Set.Icc D.a1 D.b1) :
    |D.U v - D.U v'| ≤ |v - v'| := by
  let x := v - v'
  let d := D.U v - D.U v'
  have hq₁ := D.Q_nonneg v' hv'
  have hq₂ := D.Q_le_one v' hv'
  have hq₃ := D.Q_nonneg v hv
  have hq₄ := D.Q_le_one v hv
  have hp₁ : |x * D.Q v'| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg hq₁]
    exact mul_le_of_le_one_right (abs_nonneg x) hq₂
  have hp₂ : |x * D.Q v| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg hq₃]
    exact mul_le_of_le_one_right (abs_nonneg x) hq₄
  have h₁ := D.bicB' v hv v' hv'
  have h₂ := D.bicB' v' hv' v hv
  have hlo : x * D.Q v' ≤ d := by
    change (v - v') * D.Q v' ≤ D.U v - D.U v'
    apply (le_sub_iff_add_le).2
    simpa [add_comm] using h₁
  have hhi : d ≤ x * D.Q v := by
    change D.U v - D.U v' ≤ (v - v') * D.Q v
    apply (sub_le_iff_le_add).2
    have hh : D.U v ≤ (v - v') * D.Q v + D.U v' := by linarith [h₂]
    exact hh
  apply (abs_le).2
  constructor
  · calc
      -|x| ≤ -|x * D.Q v'| := neg_le_neg hp₁
      _ ≤ x * D.Q v' := neg_abs_le _
      _ ≤ d := hlo
  · calc
      d ≤ x * D.Q v := hhi
      _ ≤ |x * D.Q v| := le_abs_self _
      _ ≤ |x| := hp₂
end MSData

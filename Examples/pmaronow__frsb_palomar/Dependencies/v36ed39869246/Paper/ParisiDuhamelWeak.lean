module
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.ParisiWeak
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.VolterraFubini
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Absolute Fubini estimates for the nonlinear weak Duhamel equation

The source is genuinely bounded and measurable, and the adjoint test is
smooth with compact support.  The lemmas below prove the absolute integral
requirements rather than treating changes of integration order formally.
-/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff
namespace Paper
theorem exists_uniform_integral_norm_sections_bound (ψ : ℝ × ℝ → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, (∫ x, ‖ψ (t, x)‖) ≤ B := by
  obtain ⟨R, hR⟩ := (hc.image continuous_snd).isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := hψ.bounded_above_of_compact_support hc
  let K : Set ℝ := Icc (-R) R
  let majorant : ℝ → ℝ := K.indicator (fun _ => M)
  have hmi : Integrable majorant := by
    exact (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  have hMb : 0 ≤ M := (norm_nonneg (ψ (0, 0))).trans (hM _)
  refine ⟨M * volume.real K, mul_nonneg hMb ENNReal.toReal_nonneg, ?_⟩
  intro t
  have hb : ∀ x : ℝ, ‖ψ (t, x)‖ ≤ majorant x := by
    intro x
    by_cases hx : x ∈ K
    · simpa [majorant, Set.indicator_of_mem hx] using hM (t, x)
    · have hz : ψ (t, x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hp
        have hr := hR x (mem_image_of_mem Prod.snd hp)
        exact hx (by simpa only [K, mem_Icc, Real.norm_eq_abs, abs_le] using hr)
      simp [majorant, Set.indicator_of_notMem hx, hz]
  have hint := norm_integral_le_of_norm_le (f := fun x => ‖ψ (t, x)‖)
    hmi (.of_forall fun x => by simpa using hb x)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hint
  apply hint.trans_eq
  unfold majorant
  rw [integral_indicator_const M measurableSet_Icc]
  simp [K, smul_eq_mul, mul_comm]
end Paper

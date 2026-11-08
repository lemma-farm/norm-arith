module
public import Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Dependencies.vd181f110d3a9.SharpWasserstein.BoundedFlow
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
@[expose] public section
/-! Synchronous first-order comparison. The additive input may be nowhere
 differentiable: it cancels before the derivative is taken. A C¹ observable
 requires no second derivative, because strict differentiability controls its
 difference at two moving points. -/
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal Interval ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
/-- Bounded drifts give a deterministic integrable dominator for the
 difference quotient; no moment or modulus assumption on the input is used. -/
theorem trajectory_difference_norm_le
    {v q : ℝ → E → E} {w X Y : ℝ → E} {x : E} {T t M A : ℝ}
    (hX : FiniteAdditiveTrajectory v w x T X)
    (hY : FiniteAdditiveTrajectory q w x T Y)
    (hv : ∀ r ∈ Icc 0 T, ∀ z, ‖v r z‖ ≤ M)
    (hq : ∀ r ∈ Icc 0 T, ∀ z, ‖q r z‖ ≤ A) (ht : t ∈ Icc 0 T) :
    ‖X t-Y t‖ ≤ (M+A)*t := by
  have hXi : IntervalIntegrable (fun r => v r (X r)) volume 0 t := (hX.driftContinuous.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hYi : IntervalIntegrable (fun r => q r (Y r)) volume 0 t := (hY.driftContinuous.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have he : X t-Y t = ∫ r in (0:ℝ)..t, v r (X r)-q r (Y r) := by
    rw [intervalIntegral.integral_sub hXi hYi,hX.equation t ht,hY.equation t ht]
    abel
  rw [he]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := t) (C := M+A) (f := fun r => v r (X r)-q r (Y r)) (by
      intro r hr
      have hrT : r ∈ Icc 0 T := ⟨(uIoc_of_le ht.1 ▸ hr).1.le,(uIoc_of_le ht.1 ▸ hr).2.trans ht.2⟩
      exact (norm_sub_le _ _).trans (add_le_add (hv r hrT _) (hq r hrT _)))
  simpa only [sub_zero,abs_of_nonneg ht.1] using hn
end SharpWasserstein.SwitchSourceDerivative

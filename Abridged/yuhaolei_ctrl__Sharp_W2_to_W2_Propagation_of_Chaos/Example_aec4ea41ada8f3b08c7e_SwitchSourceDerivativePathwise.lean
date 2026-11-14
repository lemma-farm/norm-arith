module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

-- ==== Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Dependencies.vd181f110d3a9.SharpWasserstein.FiniteTrajectory ====
public section
@[expose] public section
/-! Actual existence of continuous-forcing integral solutions on every finite
horizon for globally bounded, globally Lipschitz drifts. Picard--Lindelöf is
applied to the translated ODE, so no derivative of the forcing is assumed. -/
noncomputable section
open Set MeasureTheory Metric
open scoped Interval NNReal
namespace SharpWasserstein
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
structure FiniteAdditiveTrajectory (v : ℝ → E → E) (w : ℝ → E) (x₀ : E)
    (T : ℝ) (X : ℝ → E) : Prop where
  continuous : ContinuousOn X (Icc 0 T)
  driftContinuous : ContinuousOn (fun t => v t (X t)) (Icc 0 T)
  equation : ∀ t ∈ Icc 0 T, X t = x₀ + (∫ s in (0 : ℝ)..t, v s (X s)) + w t
end SharpWasserstein

end
end
end

-- ==== Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Examples.Example_aec4ea41ada8f3b08c7e_SwitchSourceDerivativePathwise ====
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

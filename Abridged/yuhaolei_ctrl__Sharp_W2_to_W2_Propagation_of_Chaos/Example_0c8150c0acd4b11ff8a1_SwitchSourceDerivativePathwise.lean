module

public import Mathlib
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Tactic.Linarith
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- ==== Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Examples.Example_0c8150c0acd4b11ff8a1_SwitchSourceDerivativePathwise ====
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
/-- A chain rule for a difference of two rough curves. Only their difference
is differentiable; the individual curves need merely be continuous. -/
theorem strict_test_difference_hasDerivWithinAt
    {X Y : ℝ → E} {x a : E} {s : Set ℝ} {F : E → ℝ} {D : E →L[ℝ] ℝ}
    (hX : ContinuousWithinAt X s 0) (hY : ContinuousWithinAt Y s 0)
    (hX₀ : X 0 = x) (hY₀ : Y 0 = x)
    (hXY : HasDerivWithinAt (fun t => X t-Y t) a s 0)
    (hF : HasStrictFDerivAt F D x) :
    HasDerivWithinAt (fun t => F (X t)-F (Y t)) (D a) s 0 := by
  have hp : Tendsto (fun t => (X t,Y t)) (𝓝[s] 0) (𝓝 (x,x)) := by
    simpa only [hX₀,hY₀] using hX.prodMk_nhds hY
  have hb : (fun t => X t-Y t) =O[𝓝[s] 0] (fun t : ℝ => t-0) := by
    simpa only [hX₀,hY₀,sub_self,sub_zero] using hXY.hasFDerivWithinAt.isBigO_sub
  have he := (hF.isLittleO.comp_tendsto hp).trans_isBigO hb
  have hd : HasDerivWithinAt (fun t => D (X t-Y t)) (D a) s 0 :=
    D.hasFDerivAt.comp_hasDerivWithinAt 0 hXY
  apply HasDerivWithinAt.of_isLittleO
  exact (he.add hd.isLittleO).congr_left (fun t => by
    simp only [Function.comp_def,hX₀,hY₀,sub_self,map_zero,sub_zero]
    ring)
end SharpWasserstein.SwitchSourceDerivative

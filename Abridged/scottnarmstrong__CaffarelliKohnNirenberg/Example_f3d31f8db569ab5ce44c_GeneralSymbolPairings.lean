import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Snowflaking
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.MeasureTheory.Function.L2Space

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Foundation.Parabolic.Basic ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Parabolic space-time geometry

The spatial geometry uses the Euclidean norm on `Fin 3 → ℝ`, defined from the
finite sum of squares.  This is deliberate: the ambient function space's
default norm can be the sup norm, whereas the cylinders here are Euclidean.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
abbrev Vec3 := Fin 3 → ℝ
abbrev L2Vec3 := PiLp 2 (fun _ : Fin 3 => ℝ)
def ParabolicPoint := Vec3 × ℝ
axiom half_pos : 0 < (1 / 2 : ℝ)
axiom half_le_one : (1 / 2 : ℝ) ≤ 1
abbrev SnowTime := Metric.Snowflaking ℝ (1 / 2 : ℝ) half_pos half_le_one

instance : MeasurableSpace ParabolicPoint := inferInstanceAs (MeasurableSpace (Vec3 × ℝ))
instance : MeasurableSpace SnowTime := borel SnowTime
set_option linter.unusedVariables false in
axiom _root_.CKN.Foundation.Parabolic.instBorelSpaceSnowTime : BorelSpace CKN.Foundation.Parabolic.SnowTime
attribute [instance] _root_.CKN.Foundation.Parabolic.instBorelSpaceSnowTime
def parabolicMeasurableEquiv : ParabolicPoint ≃ᵐ L2Vec3 × SnowTime :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 Vec3) {
    toEquiv := Metric.Snowflaking.toSnowflaking
    measurable_toFun := Metric.Snowflaking.continuous_toSnowflaking.measurable
    measurable_invFun := Metric.Snowflaking.homeomorph.continuous.measurable }
def parabolicMap (p : ParabolicPoint) :
    L2Vec3 × SnowTime := parabolicMeasurableEquiv p
axiom parabolicMap_injective : Function.Injective parabolicMap
noncomputable instance parabolicMetricSpace : MetricSpace ParabolicPoint :=
  MetricSpace.induced parabolicMap parabolicMap_injective inferInstance

set_option linter.unusedVariables false in
axiom _root_.CKN.Foundation.Parabolic.instBorelSpaceParabolicPoint : BorelSpace CKN.Foundation.Parabolic.ParabolicPoint
attribute [instance] _root_.CKN.Foundation.Parabolic.instBorelSpaceParabolicPoint

instance : MeasureSpace ParabolicPoint := inferInstanceAs (MeasureSpace (Vec3 × ℝ))

end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Core.HeatPotential.Kernel ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open  CKN.Foundation.Parabolic
/-! The convolution variables are written explicitly so that the causal heat
kernel and its spatial derivatives have one common interface. -/
def pointSub (w v : ParabolicPoint) : ParabolicPoint :=
  (w.1 - v.1, w.2 - v.2)
end CKN.Core.HeatPotential

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Examples.Example_f3d31f8db569ab5ce44c_GeneralSymbolPairings ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open  CKN.Foundation.Parabolic
private axiom parabolic_sub_measurePreserving (y : ParabolicPoint) :
    MeasurePreserving (fun x : ParabolicPoint => pointSub x y)
      (volume : Measure ParabolicPoint) volume
private axiom parabolic_integrableOn_shift_complex
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    {K : Set ParabolicPoint} (hK : IsCompact K) (y : ParabolicPoint) :
    IntegrableOn (fun x : ParabolicPoint => k (pointSub x y)) K volume
private lemma parabolic_setIntegral_norm_shift_le_complex
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    {K L : Set ParabolicPoint} (hK : IsCompact K) (hL : IsCompact L)
    (y : ParabolicPoint)
    (hsub : (fun x : ParabolicPoint => pointSub x y) '' K ⊆ L) :
    (∫ x in K, ‖k (pointSub x y)‖) ≤ ∫ z in L, ‖k z‖ := by
  have hkn : LocallyIntegrable (fun z : ParabolicPoint => ‖k z‖) volume := by
    intro x
    rcases hk x with ⟨U, hU, hInt⟩
    exact ⟨U, hU, hInt.norm⟩
  have hshift : IntegrableOn (fun x : ParabolicPoint =>
      ‖k (pointSub x y)‖) K volume := by
    exact (parabolic_integrableOn_shift_complex hk hK y).integrable.norm
  have hleft := hshift.integrable_indicator hK.measurableSet
  have hright0 := hkn.integrableOn_isCompact hL
  have hright := hright0.integrable_indicator hL.measurableSet
  have hcomp := (parabolic_sub_measurePreserving y).integrable_comp
    hright.aestronglyMeasurable |>.mpr hright
  have hle : ∀ᵐ x : ParabolicPoint, K.indicator
      (fun z : ParabolicPoint => ‖k (pointSub z y)‖) x ≤
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y) := by
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · have hxy : pointSub x y ∈ L := hsub ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxy]
    · rw [Set.indicator_of_notMem hx]
      by_cases hLxy : pointSub x y ∈ L
      · rw [Set.indicator_of_mem hLxy]
        exact norm_nonneg _
      · rw [Set.indicator_of_notMem hLxy]
  have hint := integral_mono_ae hleft hcomp hle
  rw [integral_indicator hK.measurableSet] at hint
  let e := (Homeomorph.subRight y.1).prodCongr (Homeomorph.subRight y.2)
  have htrans := (parabolic_sub_measurePreserving y).integral_comp
    e.measurableEmbedding (L.indicator (fun z : ParabolicPoint => ‖k z‖))
  have htrans' : (∫ x : ParabolicPoint,
      (L.indicator (fun z : ParabolicPoint => ‖k z‖) ∘
        fun x : ParabolicPoint => pointSub x y) x) =
      ∫ z : ParabolicPoint, L.indicator (fun z : ParabolicPoint => ‖k z‖) z := by
    change (∫ x : ParabolicPoint,
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y)) =
      ∫ z : ParabolicPoint, L.indicator (fun z : ParabolicPoint => ‖k z‖) z at htrans
    exact htrans
  rw [htrans', integral_indicator hL.measurableSet] at hint
  exact hint
end CKN.Core.HeatPotential

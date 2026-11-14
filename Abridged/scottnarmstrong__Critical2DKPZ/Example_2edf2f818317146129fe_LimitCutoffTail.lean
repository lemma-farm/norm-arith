module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Rev
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.va55404adc639.Critical2DKPZ.Definitions.Plane ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The plane `ℝ²`, with its Euclidean structure. -/
@[reducible] def Plane := EuclideanSpace ℝ (Fin 2)
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.va55404adc639.Critical2DKPZ.Definitions.HeatKernel ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Heat kernel `g_u(z) = (2πu)⁻¹ exp(−|z|²/(2u))` (§1.1, §1.2). -/
def heatKernel (u : ℝ) (z : Plane) : ℝ :=
  (2 * Real.pi * u)⁻¹ * Real.exp (-‖z‖ ^ 2 / (2 * u))
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.va55404adc639.Critical2DKPZ.Analysis.Heat.Basic ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The planar heat kernel has covariance `u I`, is nonnegative, and has unit mass at positive times. -/
public section
noncomputable section
open MeasureTheory
namespace Critical2DKPZ

set_option linter.unusedVariables false in
axiom _root_.Critical2DKPZ.continuous_heatKernel : ∀ (u : ℝ), Continuous (Critical2DKPZ.heatKernel u)

end Critical2DKPZ
end

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.va55404adc639.Critical2DKPZ.SHF.Tsai.Defs ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Tsai's dense-time stochastic heat-flow axioms

The flow predicate includes
measurability, almost-sure local finiteness, approximate composition, independent
increments and the first four moment formulas. It makes no path-continuity assumption.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BigOperators CompactlySupported
namespace Critical2DKPZ.SHF.Tsai

/-- `χ_R(x) = min 1 (max 0 (R + 1 − |x|))`, the intermediate-variable cutoff of the cutoff-tail estimate. -/
def ballCutoff (R : ℝ) (x : Plane) : ℝ := min 1 (max 0 (R + 1 - ‖x‖))
end Critical2DKPZ.SHF.Tsai
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.va55404adc639.Critical2DKPZ.SHF.Tsai.Cutoff ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The intermediate-variable cutoff in approximate flow -/
@[expose] public noncomputable section
open Filter Set
open scoped Topology
namespace Critical2DKPZ.SHF.Tsai

set_option linter.unusedVariables false in
axiom _root_.Critical2DKPZ.SHF.Tsai.continuous_ballCutoff : ∀ (R : ℝ), Continuous (Critical2DKPZ.SHF.Tsai.ballCutoff R)

set_option linter.unusedVariables false in
axiom _root_.Critical2DKPZ.SHF.Tsai.ballCutoff_eq_zero_of_le_norm : ∀ {R : ℝ} {x : Critical2DKPZ.Plane}, R + 1 ≤ ‖x‖ → Critical2DKPZ.SHF.Tsai.ballCutoff R x = 0

end Critical2DKPZ.SHF.Tsai
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.va55404adc639.Critical2DKPZ.SHF.Positivity.BoundedCutoff ====
public section
/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Compact cutoffs for bounded heat-start pairings -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped BoundedContinuousFunction CompactlySupported Topology
namespace Critical2DKPZ.SHF.Positivity
/-- Compactly supported cutoff of the heat-start kernel with bounded continuous terminal data. -/
def heatBoundedTerminalCutoffTest (δ : ℝ) (x : Plane) (g : Plane →ᵇ ℝ) (R : ℝ) :
    C_c(Plane × Plane, ℝ) where
  toFun p := heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2
  continuous_toFun := by
    exact (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
      (g.continuous.comp continuous_snd) |>.mul
        ((continuous_ballCutoff R).comp continuous_fst) |>.mul
          ((continuous_ballCutoff R).comp continuous_snd))
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : Plane) (R + 1)).prod
        (isCompact_closedBall (0 : Plane) (R + 1)))
    intro p hp
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hn
      have hzero : ballCutoff R p.1 = 0 :=
        ballCutoff_eq_zero_of_le_norm (le_of_lt (lt_of_not_ge hn))
      apply hp
      change heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2 = 0
      simp [hzero]
    · rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hn
      have hzero : ballCutoff R p.2 = 0 :=
        ballCutoff_eq_zero_of_le_norm (le_of_lt (lt_of_not_ge hn))
      apply hp
      change heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2 = 0
      simp [hzero]

end Critical2DKPZ.SHF.Positivity
end

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_2edf2f818317146129fe_LimitCutoffTail ====
/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # First-moment cutoff tails for limiting heat-start pairings -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open  Critical2DKPZ.SHF.Tsai
open scoped BoundedContinuousFunction ENNReal Topology
namespace Critical2DKPZ.SHF.Positivity
/-- The nonnegative remainder after cutting off both coordinates of a heat-start pairing. -/
def heatPairingCutoffTail (δ : ℝ) (x : Plane) (R : ℝ) : Plane × Plane → ℝ :=
  fun p => heatKernel δ (p.1 - x) * (1 - ballCutoff R p.1 * ballCutoff R p.2)

private def heatBoundedTerminalCutoffRemainder (δ : ℝ) (x : Plane)
    (g : Plane →ᵇ ℝ) (R : ℝ) : Plane × Plane → ℝ := fun p =>
  heatKernel δ (p.1 - x) * g p.2 * (1 - ballCutoff R p.1 * ballCutoff R p.2)
set_option linter.unusedVariables false in
/-- The integral error from a compact cutoff is bounded by the terminal sup norm times the
nonnegative two-coordinate heat-start tail. -/
theorem abs_integral_heatBoundedTerminal_cutoff_error_le
    (μ : Measure (Plane × Plane)) {δ : ℝ} (hδ : 0 < δ) (x : Plane)
    (g : Plane →ᵇ ℝ) (R : ℝ)
    (hK : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) μ) 
    (h_Critical2DKPZ_SHF_Positivity_integrable_heatKernel_mul_boundedTerminal : ∀ (μ : MeasureTheory.Measure (Critical2DKPZ.Plane × Critical2DKPZ.Plane)) {δ : ℝ},
      0 < δ →
        ∀ (x : Critical2DKPZ.Plane) (g : BoundedContinuousFunction Critical2DKPZ.Plane ℝ),
          MeasureTheory.Integrable
              (fun (p : Critical2DKPZ.Plane × Critical2DKPZ.Plane) ↦
                Critical2DKPZ.heatKernel δ (p.1 - x))
              μ →
            MeasureTheory.Integrable
              (fun (p : Critical2DKPZ.Plane × Critical2DKPZ.Plane) ↦
                Critical2DKPZ.heatKernel δ (p.1 - x) * (g : Critical2DKPZ.Plane → ℝ) p.2)
              μ)
    (h_Critical2DKPZ_SHF_Positivity_heatPairingCutoffTail_le_heatKernel : ∀ {δ : ℝ},
      0 < δ →
        ∀ (x : Critical2DKPZ.Plane) (R : ℝ) (p : Critical2DKPZ.Plane × Critical2DKPZ.Plane),
          Critical2DKPZ.SHF.Positivity.heatPairingCutoffTail δ x R p ≤
            Critical2DKPZ.heatKernel δ (p.1 - x))
    (h_Critical2DKPZ_SHF_Positivity_integrable_heatPairingCutoffTail_of_heat : ∀ {δ : ℝ},
      0 < δ →
        ∀ (x : Critical2DKPZ.Plane) (R : ℝ)
          (μ : MeasureTheory.Measure (Critical2DKPZ.Plane × Critical2DKPZ.Plane)),
          MeasureTheory.Integrable
              (fun (p : Critical2DKPZ.Plane × Critical2DKPZ.Plane) ↦
                Critical2DKPZ.heatKernel δ (p.1 - x))
              μ →
            MeasureTheory.Integrable (Critical2DKPZ.SHF.Positivity.heatPairingCutoffTail δ x R) μ)
    (h_Critical2DKPZ_SHF_Positivity_integrable_heatBoundedTerminalCutoffTest : ∀ (μ : MeasureTheory.Measure (Critical2DKPZ.Plane × Critical2DKPZ.Plane)) {δ : ℝ},
      0 < δ →
        ∀ (x : Critical2DKPZ.Plane) (g : BoundedContinuousFunction Critical2DKPZ.Plane ℝ) (R : ℝ),
          MeasureTheory.Integrable
              (fun (p : Critical2DKPZ.Plane × Critical2DKPZ.Plane) ↦
                Critical2DKPZ.heatKernel δ (p.1 - x))
              μ →
            MeasureTheory.Integrable
              (fun (p : Critical2DKPZ.Plane × Critical2DKPZ.Plane) ↦
                (Critical2DKPZ.SHF.Positivity.heatBoundedTerminalCutoffTest δ x g R :
                    Critical2DKPZ.Plane × Critical2DKPZ.Plane → ℝ)
                  p)
              μ)
    (h_Critical2DKPZ_SHF_Tsai_ballCutoff_mem_Icc : ∀ (R : ℝ) (x : Critical2DKPZ.Plane), Critical2DKPZ.SHF.Tsai.ballCutoff R x ∈ Set.Icc 0 1)
    (h_Critical2DKPZ_heatKernel_nonneg : ∀ {u : ℝ}, 0 ≤ u → ∀ (x : Critical2DKPZ.Plane), 0 ≤ Critical2DKPZ.heatKernel u x)
    :
    |(∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ) -
      ∫ p, heatBoundedTerminalCutoffTest δ x g R p ∂μ| ≤
        ‖g‖ * ∫ p, heatPairingCutoffTail δ x R p ∂μ := by
  have hFull := h_Critical2DKPZ_SHF_Positivity_integrable_heatKernel_mul_boundedTerminal μ hδ x g hK
  have hCut := h_Critical2DKPZ_SHF_Positivity_integrable_heatBoundedTerminalCutoffTest μ hδ x g R hK
  have hTail := h_Critical2DKPZ_SHF_Positivity_integrable_heatPairingCutoffTail_of_heat hδ x R μ hK
  have hrem : Integrable (heatBoundedTerminalCutoffRemainder δ x g R) μ := by
    apply (hK.const_mul ‖g‖).mono'
      (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
        (g.continuous.comp continuous_snd) |>.mul
          ((continuous_const : Continuous (fun _ : Plane × Plane => (1 : ℝ))).sub
            (((continuous_ballCutoff R).comp continuous_fst).mul
              ((continuous_ballCutoff R).comp continuous_snd))) |>.measurable.aestronglyMeasurable)
    filter_upwards [] with p
    have hk := h_Critical2DKPZ_heatKernel_nonneg hδ.le (p.1 - x)
    have h1 := h_Critical2DKPZ_SHF_Tsai_ballCutoff_mem_Icc R p.1
    have h2 := h_Critical2DKPZ_SHF_Tsai_ballCutoff_mem_Icc R p.2
    have hprod : 0 ≤ ballCutoff R p.1 * ballCutoff R p.2 ∧
        ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by
      constructor
      · exact mul_nonneg h1.1 h2.1
      · calc
          ballCutoff R p.1 * ballCutoff R p.2 ≤ ballCutoff R p.1 * 1 :=
            mul_le_mul_of_nonneg_left h2.2 h1.1
          _ ≤ 1 := by simpa using h1.2
    have hfac : 0 ≤ 1 - ballCutoff R p.1 * ballCutoff R p.2 ∧
        1 - ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by constructor <;> linarith
    change |heatKernel δ (p.1 - x) * g p.2 *
      (1 - ballCutoff R p.1 * ballCutoff R p.2)| ≤ _
    rw [abs_mul, abs_mul, abs_of_nonneg hk, abs_of_nonneg hfac.1]
    calc
      heatKernel δ (p.1 - x) * |g p.2| *
          (1 - ballCutoff R p.1 * ballCutoff R p.2) ≤
        heatKernel δ (p.1 - x) * ‖g‖ *
          (1 - ballCutoff R p.1 * ballCutoff R p.2) := by
            calc
              _ ≤ (heatKernel δ (p.1 - x) * ‖g‖) *
                  (1 - ballCutoff R p.1 * ballCutoff R p.2) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2) hk) hfac.1
              _ = _ := by ring
      _ = ‖g‖ * heatPairingCutoffTail δ x R p := by
        dsimp [heatPairingCutoffTail]
        ring
      _ ≤ ‖g‖ * heatKernel δ (p.1 - x) :=
        mul_le_mul_of_nonneg_left (h_Critical2DKPZ_SHF_Positivity_heatPairingCutoffTail_le_heatKernel hδ x R p)
          (norm_nonneg _)
  have hdiff : (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2 -
      heatBoundedTerminalCutoffTest δ x g R p) =
      heatBoundedTerminalCutoffRemainder δ x g R := by
    funext p
    change heatKernel δ (p.1 - x) * g p.2 -
      (heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2) =
      heatKernel δ (p.1 - x) * g p.2 *
        (1 - ballCutoff R p.1 * ballCutoff R p.2)
    ring
  have hremInt : Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2 -
        heatBoundedTerminalCutoffTest δ x g R p) μ := hFull.sub hCut
  have hEq : (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ) -
      ∫ p, heatBoundedTerminalCutoffTest δ x g R p ∂μ =
      ∫ p, heatBoundedTerminalCutoffRemainder δ x g R p ∂μ := by
    rw [← integral_sub hFull hCut]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => congrFun hdiff p)
  calc
    |(∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ) -
      ∫ p, heatBoundedTerminalCutoffTest δ x g R p ∂μ| =
      ‖∫ p, heatBoundedTerminalCutoffRemainder δ x g R p ∂μ‖ := by
        rw [hEq, Real.norm_eq_abs]
    _ ≤ ∫ p, ‖heatBoundedTerminalCutoffRemainder δ x g R p‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ p, ‖g‖ * heatPairingCutoffTail δ x R p ∂μ := by
      apply integral_mono hrem.norm (hTail.const_mul ‖g‖)
      intro p
      have hk := h_Critical2DKPZ_heatKernel_nonneg hδ.le (p.1 - x)
      have h1 := h_Critical2DKPZ_SHF_Tsai_ballCutoff_mem_Icc R p.1
      have h2 := h_Critical2DKPZ_SHF_Tsai_ballCutoff_mem_Icc R p.2
      have hfac : 0 ≤ 1 - ballCutoff R p.1 * ballCutoff R p.2 := by
        have hprod0 := mul_nonneg h1.1 h2.1
        have hprod1 : ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by
          calc
            ballCutoff R p.1 * ballCutoff R p.2 ≤ ballCutoff R p.1 * 1 :=
              mul_le_mul_of_nonneg_left h2.2 h1.1
            _ ≤ 1 := by simpa using h1.2
        linarith
      change ‖heatKernel δ (p.1 - x) * g p.2 *
        (1 - ballCutoff R p.1 * ballCutoff R p.2)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hk, abs_of_nonneg hfac]
      calc
        heatKernel δ (p.1 - x) * |g p.2| *
            (1 - ballCutoff R p.1 * ballCutoff R p.2) ≤
          heatKernel δ (p.1 - x) * ‖g‖ *
            (1 - ballCutoff R p.1 * ballCutoff R p.2) := by
              calc
                _ ≤ (heatKernel δ (p.1 - x) * ‖g‖) *
                    (1 - ballCutoff R p.1 * ballCutoff R p.2) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2) hk) hfac
                _ = _ := by ring
        _ = ‖g‖ * heatPairingCutoffTail δ x R p := by
          dsimp [heatPairingCutoffTail]
          ring
    _ = ‖g‖ * ∫ p, heatPairingCutoffTail δ x R p ∂μ := integral_const_mul _ _
end Critical2DKPZ.SHF.Positivity
end

module

public import Mathlib
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.Homogenization.Ambient.Basic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open scoped BigOperators
namespace Homogenization
abbrev Vec (d : ℕ) := Fin d → ℝ

end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Flow.IsFlow ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `IsFlow` (Flow).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open Homogenization
namespace AVenhance
/-- Flow of a time-dependent field `b` on `ℝ²`: `X t x s` solves
`∂ₜ X(t,x,s) = b(t, X(t,x,s))` for all `t ∈ ℝ`, with `X(s,x,s) = x`
(source: `e.flow.m.def`, `enhance.tex` 1397-1410). -/
def IsFlow (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2) : Prop :=
  (∀ x s, X s x s = x) ∧
  (∀ x s t, HasDerivAt (fun r => X r x s) (b t (X t x s)) t)
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_0af13890aadfa01644cb_FlowCurve ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The characterized flow as an actual compact-time solution curve. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory Set
open scoped NNReal
namespace AVenhance.Infra.Section4

def amnrFlowCurve {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X) (s a c : ℝ) (x : Vec 2) : C(Icc a c, Vec 2) :=
  ⟨fun t => X t x s,
    (continuous_iff_continuousAt.mpr (fun t => (hX.2 x s t).continuousAt)).comp continuous_subtype_val⟩
set_option linter.unusedVariables false in
/-- Grönwall gives actual uniform continuity of the solution-curve family
with respect to its initial point, before proving any flow derivatives. -/
theorem amnrFlowCurve_lipschitz {b : ℝ → Vec 2 → Vec 2}
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {L : ℝ} (hL₀ : 0 ≤ L) (hL : ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {s a c : ℝ} (hs : s ∈ Icc a c) 
    (h_AVenhance_Infra_Flow_flow_spatial_gronwall : ∀ (b : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2) {L : ℝ},
      (∀ (u : ℝ) (x y : Homogenization.Vec 2), ‖b u x - b u y‖ ≤ L * ‖x - y‖) →
        ∀ {X : ℝ → Homogenization.Vec 2 → ℝ → Homogenization.Vec 2},
          AVenhance.IsFlow b X →
            ∀ (x y : Homogenization.Vec 2) (s t : ℝ),
              ‖X t x s - X t y s‖ ≤ Real.exp (L * |t - s|) * ‖x - y‖)
    :
    LipschitzWith (Real.exp (L * (c - a))).toNNReal (amnrFlowCurve hX s a c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le]
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro t
  change ‖X t x s - X t y s‖ ≤ _
  have ht : |(t : ℝ) - s| ≤ c - a :=
    abs_le.mpr ⟨by linarith [hs.2, t.property.1], by linarith [hs.1, t.property.2]⟩
  exact (h_AVenhance_Infra_Flow_flow_spatial_gronwall b hL hX x y s t).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hL₀)) (norm_nonneg _))
end AVenhance.Infra.Section4

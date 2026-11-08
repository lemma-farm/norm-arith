-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Statements.Flow.IsFlow
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.FaaDiBruno.Composition
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.Laws
public import Mathlib
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Characteristic identities for smooth solutions of the transport equation. -/
@[expose] public section
open Homogenization MeasureTheory
open scoped ContDiff NNReal Topology
noncomputable section
namespace AVenhance.FaaDiBruno
structure IsClassicalTransportSolution
    (b g Y : ℝ → Vec 2 → Vec 2) : Prop where
  smooth : ContDiff ℝ ∞ (Function.uncurry Y)
  equation : ∀ t x,
    fderiv ℝ (Function.uncurry Y) (t, x) (1, b t x) = g t x
  initial : ∀ x, Y 0 x = 0
end AVenhance.FaaDiBruno
end

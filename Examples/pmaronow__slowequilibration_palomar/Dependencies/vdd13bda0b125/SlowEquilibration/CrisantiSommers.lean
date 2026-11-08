-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
namespace SlowEquilibration.CrisantiSommers
open MeasureTheory Set Filter
open scoped Topology
/-- A support cutoff in the manuscript's class of variational measures. -/
def HasCutoff (ζ : Measure ℝ) (q : ℝ) : Prop :=
  0 ≤ q ∧ q < 1 ∧ ∀ᵐ s ∂ζ, s ∈ Icc (0:ℝ) q
/-- The actual integrated distribution function, expressed using the
Fubini kernel from the manuscript. -/
noncomputable def xHat (ζ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ s, 1-max t s ∂ζ
end SlowEquilibration.CrisantiSommers

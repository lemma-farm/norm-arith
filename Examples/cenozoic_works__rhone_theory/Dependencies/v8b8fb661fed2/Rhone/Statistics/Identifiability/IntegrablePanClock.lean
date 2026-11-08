/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v8b8fb661fed2.Rhone.Statistics.Identifiability.IntegrablePanModel
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Cumulative clocks and decay for the AC/AE pan model -/
@[expose] public section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability
noncomputable def integrablePanClock (rate : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, panZeroExtension rate s
structure ProperIntegrablePanModel where
  rate : ℝ → ℝ
  pre : IntegrablePanPreModel rate
  clock_diverges : Tendsto (integrablePanClock rate) atTop atTop
end Rhone.Statistics.Identifiability

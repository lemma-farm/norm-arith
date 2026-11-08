/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v8b8fb661fed2.Rhone.Statistics.Identifiability.PanFiveData
public import Examples.cenozoic_works__rhone_theory.Dependencies.v8b8fb661fed2.Rhone.Statistics.Identifiability.IntegratedClock
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # A universal fifth-sample panmictic spectrum inequality -/
@[expose] public section
open scoped ENNReal
open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false
structure PanFiveForwardSystem where
  rate : ℝ → ℝ
  rate_nonneg : ∀ t, 0 ≤ rate t
  rate_locallyIntegrable : LocallyIntegrable rate volume
  mass : ℝ → PanFiveState → ℝ
  initial_mass : ∀ i, mass 0 i = if i = 0 then 1 else 0
  mass_nonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ mass t i
  mass_ac : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun x => mass x i) 0 t
  mass_equation : ∀ t, 0 ≤ t → ∀ᵐ x, x ∈ uIcc 0 t → ∀ i,
    HasDerivAt (fun y => mass y i) (∑ j, mass x j * panFiveGenerator (rate x) j i) x
end Rhone.Statistics.Identifiability

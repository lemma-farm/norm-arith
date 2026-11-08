/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # The three-tip finite-sequence channel -/
@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Rhone.Statistics.ThreeTipSites
abbrev Triple (K : ℕ) := Fin K × (Fin K × Fin K)
abbrev Panel (K L : ℕ) := Fin L → Triple K
end Rhone.Statistics.ThreeTipSites

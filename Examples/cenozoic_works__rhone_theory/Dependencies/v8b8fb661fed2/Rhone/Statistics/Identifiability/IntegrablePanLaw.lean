/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v8b8fb661fed2.Rhone.Statistics.Identifiability.AEDensityMarginals
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Joint laws for the AC/AE pan model -/
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false
namespace IntegrablePanPreModel
variable {rate : ℝ → ℝ} (P : IntegrablePanPreModel rate)
end IntegrablePanPreModel
namespace ProperIntegrablePanModel
variable (P : ProperIntegrablePanModel)
end ProperIntegrablePanModel
end Rhone.Statistics.Identifiability

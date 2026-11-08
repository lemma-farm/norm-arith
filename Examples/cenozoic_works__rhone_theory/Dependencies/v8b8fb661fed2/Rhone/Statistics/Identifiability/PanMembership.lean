/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v8b8fb661fed2.Rhone.Statistics.Identifiability.ScalarPanModel
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # A measure-level scalar membership theorem at a specified positive pair clock -/
@[expose] public section
open Set MeasureTheory Filter
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false
end Rhone.Statistics.Identifiability

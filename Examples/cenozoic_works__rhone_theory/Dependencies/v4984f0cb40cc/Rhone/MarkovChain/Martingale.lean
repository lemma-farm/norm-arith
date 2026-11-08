/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.MarkovChain.Hitting
public import Mathlib
public import Mathlib.Probability.Process.HittingTime
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Martingales from harmonic functions and optional stopping -/
@[expose] public section
namespace Rhone.MarkovChain.FinChain
open MeasureTheory ProbabilityTheory Finset Filter Topology
variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {C : FinChain S} {h : S → ℝ}
end Rhone.MarkovChain.FinChain

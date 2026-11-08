/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.MarkovChain.AbsorptionProb
public import Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.MarkovChain.Trajectory
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Absorption as a statement about trajectories -/
@[expose] public section
namespace Rhone.MarkovChain.FinChain
open MeasureTheory ProbabilityTheory Finset Filter Topology
variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {C : FinChain S} {A : Finset S}
end Rhone.MarkovChain.FinChain

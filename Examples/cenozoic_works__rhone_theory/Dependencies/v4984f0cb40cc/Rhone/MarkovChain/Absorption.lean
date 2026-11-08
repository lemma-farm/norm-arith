/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.MarkovChain.FinChain
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Absorbing states and the decay of the survival probability -/
@[expose] public section
namespace Rhone.MarkovChain.FinChain
open Finset Filter Topology
variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)
variable {C} {A : Finset S}
end Rhone.MarkovChain.FinChain

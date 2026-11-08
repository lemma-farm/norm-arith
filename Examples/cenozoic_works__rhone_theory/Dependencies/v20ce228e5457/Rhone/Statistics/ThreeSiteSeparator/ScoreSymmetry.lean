/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib
public import Examples.cenozoic_works__rhone_theory.Dependencies.v20ce228e5457.Rhone.Statistics.ThreeTipSites.Channel
public import Examples.cenozoic_works__rhone_theory.Dependencies.v20ce228e5457.Rhone.Statistics.ThreeSiteSeparator.ObservableAlgebra
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Score means for every shared cherry, using explicit finite relabelling -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites                  
def uScore {K : ℕ} (e : Fin 3) (x : Triple K) : ℝ :=
  ![pairScore K x.1 x.2.1, pairScore K x.1 x.2.2, pairScore K x.2.1 x.2.2] e
def vScore {K : ℕ} (x : Triple K) : ℝ := tripleScore K x.1 x.2.1 x.2.2
end Rhone.Statistics.ThreeSiteSeparator

/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib
public import Examples.cenozoic_works__rhone_theory.Dependencies.v20ce228e5457.Rhone.Statistics.ThreeTipSites.Channel
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Finite-block expectation algebra with one topology shared by all sites -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites                  
def threeProduct {K : ℕ} (f g h : Triple K → ℝ) (x : Panel K 3) : ℝ :=
  f (x 0)*g (x 1)*h (x 2)
end Rhone.Statistics.ThreeSiteSeparator

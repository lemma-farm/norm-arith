/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib
public import Examples.cenozoic_works__rhone_theory.Dependencies.v20ce228e5457.Rhone.Statistics.ThreeTipSites.Channel
public import Examples.cenozoic_works__rhone_theory.Dependencies.v20ce228e5457.Rhone.Statistics.ThreeSiteSeparator.BlockStatistics
public import Examples.cenozoic_works__rhone_theory.Dependencies.v20ce228e5457.Rhone.Statistics.ThreeSiteRobustness.FeatureBounds
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Uniform total-variation margin between island and pan three-site pattern scores -/
@[expose] public section
open MeasureTheory Set Filter
namespace Rhone.Statistics.ThreeSiteRobustness
open                  ThreeSiteSeparator ThreeTipSites                        
noncomputable def panelFeatures {K : ℕ} : Fin 5 → Panel K 3 → ℝ :=
  ![aStat, p2Stat, p3Stat, hStat, jStat]
theorem panelFeatures_bounded {K : ℕ} (hK : 3 ≤ K) (i : Fin 5) (x : Panel K 3) :
    |panelFeatures i x| ≤ 1 := by
  have h := feature_bounds hK x
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2
end Rhone.Statistics.ThreeSiteRobustness

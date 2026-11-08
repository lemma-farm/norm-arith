/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib
public import Examples.cenozoic_works__rhone_theory.Dependencies.v20ce228e5457.Rhone.Statistics.ThreeTipSites.Channel
public import Examples.cenozoic_works__rhone_theory.Dependencies.v20ce228e5457.Rhone.Statistics.ThreeSiteSeparator.BlockExpectations public import Examples.cenozoic_works__rhone_theory.Dependencies.v20ce228e5457.Rhone.Statistics.ThreeSiteSeparator.ScoreSymmetry
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # The five explicit three-site pattern statistics and fixed-cherry means -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites                  
def aStat {K : ℕ} (x : Panel K 3) : ℝ :=
  (threeProduct (uScore 0) (fun _ => 1) (fun _ => 1) x +
    threeProduct (uScore 1) (fun _ => 1) (fun _ => 1) x +
    threeProduct (uScore 2) (fun _ => 1) (fun _ => 1) x)/3
def p2Stat {K : ℕ} (x : Panel K 3) : ℝ :=
  (threeProduct (uScore 0) (uScore 0) (fun _ => 1) x +
    threeProduct (uScore 1) (uScore 1) (fun _ => 1) x +
    threeProduct (uScore 2) (uScore 2) (fun _ => 1) x)/3
def p3Stat {K : ℕ} (x : Panel K 3) : ℝ :=
  (threeProduct (uScore 0) (uScore 0) (uScore 0) x +
    threeProduct (uScore 1) (uScore 1) (uScore 1) x +
    threeProduct (uScore 2) (uScore 2) (uScore 2) x)/3
def hStat {K : ℕ} (x : Panel K 3) : ℝ :=
  (threeProduct vScore (uScore 0) (uScore 0) x +
    threeProduct vScore (uScore 1) (uScore 1) x +
    threeProduct vScore (uScore 2) (uScore 2) x)/3
def jStat {K : ℕ} (x : Panel K 3) : ℝ :=
  (threeProduct vScore (uScore 0) (uScore 1) x +
    threeProduct vScore (uScore 0) (uScore 2) x +
    threeProduct vScore (uScore 1) (uScore 0) x +
    threeProduct vScore (uScore 1) (uScore 2) x +
    threeProduct vScore (uScore 2) (uScore 0) x +
    threeProduct vScore (uScore 2) (uScore 1) x)/6
end Rhone.Statistics.ThreeSiteSeparator

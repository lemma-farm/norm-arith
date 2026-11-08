/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v8b8fb661fed2.Rhone.Statistics.Identifiability.PanPostPair
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Deterministic-clock survival from absolutely continuous forward equations -/
@[expose] public section
open scoped NNReal Topology
open Set Filter MeasureTheory Finset
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false
theorem ac_comp_lipschitzOn (f g : ℝ → ℝ) {a b : ℝ} (D : Set ℝ) {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzOnWith K g D)
    (hm : ∀ x ∈ uIcc a b, f x ∈ D) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b :=
  hg.comp_absolutelyContinuousOnInterval hm hf
theorem ac_exp {H : ℝ → ℝ} {a b : ℝ} (hH : AbsolutelyContinuousOnInterval H a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (H x)) a b := by
  obtain ⟨C,hC⟩ := hH.exists_bound
  have hdiff : ContDiffOn ℝ 1 Real.exp (Icc (-C) C) := Real.contDiff_exp.contDiffOn
  obtain ⟨K,hK⟩ := hdiff.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  apply ac_comp_lipschitzOn H Real.exp (Icc (-C) C) hH hK
  intro x hx
  simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using hC x hx
end Rhone.Statistics.Identifiability

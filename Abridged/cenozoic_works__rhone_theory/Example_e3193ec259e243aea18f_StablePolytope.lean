module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Tactic

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_e3193ec259e243aea18f_StablePolytope ====
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Stable finite convex representations -/
@[expose] public section
open Set Filter
open scoped Topology BigOperators
namespace Rhone.Algebra.FinitePanelGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem exists_pos_half_norm_lt_apply (f : E →L[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ y : E, ‖y‖ < 1 ∧ ‖f‖ / 2 < f y := by
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  obtain ⟨y, hy, hfy⟩ := f.exists_lt_apply_of_lt_opNorm (by linarith : ‖f‖ / 2 < ‖f‖)
  by_cases h : 0 ≤ f y
  · exact ⟨y, hy, by simpa only [Real.norm_eq_abs, abs_of_nonneg h] using hfy⟩
  · refine ⟨-y, by simpa using hy, ?_⟩
    simpa only [map_neg, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge h)] using hfy
end Rhone.Algebra.FinitePanelGeometry

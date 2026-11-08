/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Instances.NNReal.Lemmas
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Compact sets of continuous paths with values in `[0, 1]` -/
@[expose] public section
namespace Rhone.Analysis
open Set Filter Topology Metric
open scoped NNReal
def ModulusAt (j : ℕ) (d : ℝ) (f : ℝ≥0 → ℝ) : Prop :=
  ∀ s t : ℝ≥0, (s : ℝ) ≤ j + 1 → (t : ℝ) ≤ j + 1 → dist s t ≤ d → dist (f s) (f t) ≤ 1 / (j + 1)
theorem ModulusAt.mono {j : ℕ} {d d' : ℝ} {f : ℝ≥0 → ℝ} (h : ModulusAt j d f) (hd : d' ≤ d) :
    ModulusAt j d' f :=
  fun s t hs ht hst => h s t hs ht (hst.trans hd)
end Rhone.Analysis

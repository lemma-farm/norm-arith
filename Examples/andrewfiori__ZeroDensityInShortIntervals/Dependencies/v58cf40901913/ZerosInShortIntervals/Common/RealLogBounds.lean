/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-! # Small reusable numeric `Real.log` bounds

Three small numeric facts (`2 < log x` for `8 < x`, `1 < log x` for `3 ≤ x`, and `4 ≤ log x` for
`55 ≤ x`), each needed at several call sites that would otherwise re-derive `Real.exp 2 < 8`,
`Real.exp 1 < 3` or `Real.exp 4 < 55` from `Real.exp_one_lt_d9` inline. They are collected here so
that the derivation happens once; each theorem's `Used by` lists its call sites.

Also here: the elementary analysis behind Bellotti–Wong's lower bound `L(h,t)` on
`N(t+h) − N(t−h)` — the power series of `φ(x) = (1+x)log(1+x) − (1−x)log(1−x)`
(`hasSum_two_mul_sub_bwPhi`), the sharp inequality `2x − φ(x) ≤ 2(1−log 2)x³` on `[0,1)`
(`two_mul_sub_bwPhi_le`), the resulting bound on `M(t+h) − M(t−h)` for the Riemann–von Mangoldt
main term `M` (`bwM_sub_ge`), and the assembly `bw_Lbound_of_cor` that
`ExternalFacts.bellotti_wong_Lbound_le` applies to the cited Corollary 1.3.

Two integral facts about `log(1 − v²)` sit here too: the crude estimate
`integral_neg_log_one_sub_sq_le` and the exact antiderivative
`hasDerivAt_log_one_sub_sq_antideriv` / `integral_log_one_sub_sq`. They belong to the same
`L(h,t)` circle of ideas but are not on the route the assembly above takes, which needs no
integral at all; see their own docstrings. -/
noncomputable def bwM (T : ℝ) : ℝ := T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))

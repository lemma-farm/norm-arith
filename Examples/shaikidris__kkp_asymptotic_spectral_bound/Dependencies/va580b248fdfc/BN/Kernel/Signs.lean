/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.BN.Kernel.Data
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.BN.Kernel.SM
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# Sign lemmas for the kernel auxiliaries `P` and `Z`

The expansions and nonnegativity statements for `P` and `Z` in `docs/sol.tex` §3
(`eq:functions`, after `eq:factor`).
-/
namespace BN
open Finset
open scoped BigOperators
noncomputable section
variable {k : ℕ} (t q : Fin k → ℝ)
/-! ### Truncated squares -/
end
end BN

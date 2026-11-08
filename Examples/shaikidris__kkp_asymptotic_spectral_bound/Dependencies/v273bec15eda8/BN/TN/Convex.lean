/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.TN.Basic
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity
@[expose] public section
/-!
# Convex vanishing at zero and total nonnegativity

Lemma `lem:convex` of `docs/sol.tex`: if `f : [0, ∞) → [0, ∞)` is convex and
`f 0 = 0`, then for `0 < t₁ ≤ ⋯ ≤ tₖ` the matrix with rows `(1, tᵢ, f tᵢ)` is
totally nonnegative.
-/
open Function Matrix Set
namespace BN
variable {f : ℝ → ℝ}
/-! ### TN14: monotonicity of `f` and of `f t / t` -/
end BN

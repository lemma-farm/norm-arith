/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.Basic.Inner
@[expose] public section
/-!
# Ordered spectrum of a Hermitian matrix

This file records the ordered real spectrum of a Hermitian matrix, matching the
conventions in `docs/sol.tex`. The ordered family is Mathlib's antitone
`eigenvalues₀`, which is the paper's `λ₁ ≥ ⋯ ≥ λₙ` with `λ₁` at index `0`.
`F` is the sum of squares of the two largest positive eigenvalues, with missing
terms replaced by zero.
-/
namespace BN
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}
/-- The eigenvalues of a Hermitian matrix in nonincreasing order. The value at
`i` is the paper's `λ_{i+1}`. -/
noncomputable def eigs₀ (hA : A.IsHermitian) : Fin (Fintype.card n) → ℝ :=
  hA.eigenvalues₀
/-- The largest eigenvalue `λ₁(A)`. -/
noncomputable def lambdaMax (hA : A.IsHermitian) [Nonempty n] : ℝ :=
  eigs₀ hA ⟨0, Fintype.card_pos⟩
/-- The second-largest eigenvalue `λ₂(A)`. -/
noncomputable def lambdaSecond (hA : A.IsHermitian) [Nontrivial n] : ℝ :=
  eigs₀ hA ⟨1, Fintype.one_lt_card⟩
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
end BN

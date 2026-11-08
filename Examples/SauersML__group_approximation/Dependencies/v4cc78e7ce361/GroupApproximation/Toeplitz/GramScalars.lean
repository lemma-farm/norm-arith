/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
set_option warningAsError true
/-!
# Scalar identities for two isometries with orthogonal ranges

For a unit vector `η` with coordinates `a_i`, the vectors `e_i − conj(a_i) η` have the Gram matrix
`gram a i j = δ_ij − a_i conj(a_j)`, and `∑_{i,j} c_i d_j (gram a i j)²` is computed in
`sum_gram_mul_gram`.  On two blocks of three coordinates, with `βI = ∑ |a_i|²` and `τI = ∑ a_i²`
on the first block and `βJ`, `τJ` on the second, the constants `isoR`, `isoS` and `isoG` make three
such sums equal to `1`, `0` and `1` (`blockCoeff_one_one`, `blockCoeff_one_two`,
`blockCoeff_two_two`).  The constants are bounded and depend continuously on `βI`, `βJ`, `τI`, `τJ`.
-/
namespace GroupApproximation.Toeplitz
noncomputable section
open scoped ComplexConjugate
variable {κ : Type*}
/-- `δ_ij − a_i conj(a_j)`. -/
def gram [DecidableEq κ] (a : κ → ℂ) (i j : κ) : ℂ :=
  (if i = j then 1 else 0) - a i * conj (a j)
def blockV (β : ℝ) (τ : ℂ) : ℝ := 3 - 2 * β + ‖τ‖ ^ 2
/-- `C = τI conj(τJ)`. -/
def isoC (τI τJ : ℂ) : ℂ := τI * conj τJ
/-- `W = U − |C|²/V`. -/
def isoW (βI βJ : ℝ) (τI τJ : ℂ) : ℝ := blockV βJ τJ - ‖isoC τI τJ‖ ^ 2 / blockV βI τI
/-- `r = 1/√V`. -/
def isoR (βI : ℝ) (τI : ℂ) : ℝ := 1 / Real.sqrt (blockV βI τI)
/-- `s = 1/√W`. -/
def isoS (βI βJ : ℝ) (τI τJ : ℂ) : ℝ := 1 / Real.sqrt (isoW βI βJ τI τJ)
/-- `g = s C / V`. -/
def isoG (βI βJ : ℝ) (τI τJ : ℂ) : ℂ :=
  (isoS βI βJ τI τJ : ℂ) * isoC τI τJ / (blockV βI τI : ℂ)
end
end GroupApproximation.Toeplitz

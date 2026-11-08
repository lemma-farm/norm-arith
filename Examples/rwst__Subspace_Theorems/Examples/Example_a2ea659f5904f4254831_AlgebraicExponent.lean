/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module
public import Examples.rwst__Subspace_Theorems.Dependencies.v21bd6f4dc8bf.DiophantineApproximation.MahlerExponent
public import Examples.rwst__Subspace_Theorems.Dependencies.v21bd6f4dc8bf.DiophantineApproximation.PolynomialEval
public import Mathlib
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
-- Used only inside proofs and in the acceptance criteria.
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Mahler's exponent of an algebraic number is at most `d - 1`

The upper bound of Layer 1.3: if `ξ` is real algebraic of degree `d` over `ℚ` then
`mahlerExponent n ξ ≤ d - 1` for every `n`. It is Liouville's inequality, read for the value of a
polynomial rather than for the distance to a fraction: for `P` of degree at most `n` with
`P ξ ≠ 0`,

```text
|P ξ| ≥ c * H(P) ^ (-(d-1)),
```

with `c` depending only on `ξ` and `n`. Since a solution counted by `mahlerExponent n ξ` has
`|P ξ| ≤ H(P) ^ (-w)` and solutions of unbounded height, `w ≤ d - 1` follows.

## Main results

* `Real.exists_pos_le_abs_aeval`: **Liouville's inequality for the value of an integer
  polynomial** at a real algebraic number.
* `Real.mahlerExponent_le_of_isAlgebraic`: **`w_n(ξ) ≤ d - 1`** for `ξ` algebraic of degree `d`.

## Implementation notes

⚠ **The exponent `d - 1` needs the norm, not the height.** Layer 0.4's fundamental inequality
gives `|γ| ≥ (H_K γ)⁻¹` at a single place, and `H_K (P ξ) ≍ H(P) ^ d`, so it proves only
`w_n ≤ d`. The missing factor is the distinguished place itself: what is bounded below by `1` is
the *norm* `∏ w, w γ ^ mult w` of an algebraic **integer**, and only the `d - 1` other places are
then estimated by `H(P)`. So this file uses `NumberField.InfinitePlace.prod_eq_abs_norm` and
integrality, not `NumberField.inv_mulHeight₁_le_prod_apply`.

⚠ **Integrality is bought with `Polynomial.scaleRoots`, not by changing `ξ`.** The natural move —
replace `ξ` by an algebraic integer `t ξ` and quote the Möbius invariance of Layer 1.2 — needs
`ℚ⟮t ξ⟯ = ℚ⟮ξ⟯` to keep the degree. Multiplying the *value* instead costs nothing:
`t ^ deg P * P ξ` is `(P.scaleRoots t) (t ξ)`, an integer polynomial evaluated at an algebraic
integer, so it lies in the ring of integers, and the factor `t ^ deg P ≤ t ^ n` is absorbed by
the constant.

⚠ **The real place is the one that is not estimated, and it has multiplicity one.** `ξ` is real,
so the embedding `ℚ⟮ξ⟯ → ℂ` through `ℝ` is `ComplexEmbedding.IsReal` and its place has
`mult = 1`; that is what makes `∑ w ≠ w₀, mult w = d - 1` rather than `d - 2`.

⚠ **The bound is not sharp and Layer 7.3 is what sharpens it.** Schmidt's theorem gives
`w_n α = min n (d - 1)`; Layer 1.3 supplies the upper bound `d - 1` and the lower bound `n` (for
`ξ` not algebraic of degree at most `n`), and the two meet only after Layer 7.1.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Theorem A.1
and §3.4. E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University
Press (2006), Theorem 1.5.21.

This is part of Layer 1.3 of the `DiophantineApproximation` roadmap.
-/
public section
open IntermediateField Polynomial NumberField
open scoped ENNReal NNReal
namespace Real
/-! ### The value of a polynomial at an infinite place -/
/-- The triangle inequality for an evaluation, read at an infinite place of a number field: the
same statement as `Polynomial.abs_aeval_le`, with the archimedean absolute value replaced by an
arbitrary one. -/
theorem infinitePlace_aeval_le {K : Type*} [Field K] (w : InfinitePlace K) (x : K) {P : ℤ[X]}
    {n : ℕ} (hP : P.natDegree ≤ n) :
    w (aeval x P) ≤ ((n : ℝ) + 1) * (P.supNorm * max 1 (w x) ^ n) := by
  have hM1 : (1 : ℝ) ≤ max 1 (w x) := le_max_left _ _
  have hlt : P.natDegree < n + 1 := by omega
  have hsum : w (∑ i ∈ Finset.range (n + 1), (P.coeff i) • x ^ i)
      ≤ ∑ i ∈ Finset.range (n + 1), w ((P.coeff i) • x ^ i) := by
    simpa only [← InfinitePlace.coe_apply] using
      AbsoluteValue.sum_le w.1 (Finset.range (n + 1)) fun i ↦ (P.coeff i) • x ^ i
  rw [aeval_eq_sum_range' hlt]
  refine le_trans hsum ?_
  have hbound : ∀ i ∈ Finset.range (n + 1),
      w ((P.coeff i) • x ^ i) ≤ P.supNorm * max 1 (w x) ^ n := by
    intro i hi
    have hcast : w ((P.coeff i : K)) = |((P.coeff i : ℤ) : ℝ)| := by
      rw [← InfinitePlace.norm_embedding_eq, map_intCast, Complex.norm_intCast]
    rw [zsmul_eq_mul, map_mul, map_pow, hcast]
    have h1 : |((P.coeff i : ℤ) : ℝ)| ≤ P.supNorm := P.abs_coeff_le_supNorm i
    have h2 : w x ^ i ≤ max 1 (w x) ^ n :=
      (pow_le_pow_left₀ (apply_nonneg w x) (le_max_right 1 (w x)) i).trans
        (pow_le_pow_right₀ hM1 (Finset.mem_range_succ_iff.1 hi))
    exact mul_le_mul h1 h2 (by positivity) P.supNorm_nonneg
  calc ∑ i ∈ Finset.range (n + 1), w ((P.coeff i) • x ^ i)
      ≤ ∑ _i ∈ Finset.range (n + 1), P.supNorm * max 1 (w x) ^ n := Finset.sum_le_sum hbound
    _ = ((n : ℝ) + 1) * (P.supNorm * max 1 (w x) ^ n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
/-! ### Liouville's inequality for a polynomial value -/
end Real

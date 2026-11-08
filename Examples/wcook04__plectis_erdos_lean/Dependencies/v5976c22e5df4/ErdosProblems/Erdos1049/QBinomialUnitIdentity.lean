import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
set_option pp.unicode.fun true
/-!
# Erdős #1049: finite q-binomial algebra for the 2004 small-p unit

Zudilin, Acta Arith. 111 (2004), displays (8)–(11).  After the published
integrality exponent `M` is removed, the second source coefficient is a
unit at `p = 0`.  The new algebra is the finite q-binomial theorem, the
vanishing range for exponents that hit `1`, and the constant term of
`(q^α; q)_n` for `α ≥ 1`.  This module Lean-checks those identities.  It
does not construct the source sums `A(p), B(p)`, does not prove
irrationality of `F(3/2)`, and is not the 2016 Hankel family.

The Gaussian binomial uses the same Pascal recurrence as
`AdelicHeightBridge.zudilinQBinomialPS`, as a ring element rather than a
power series.
-/
open scoped BigOperators
open Finset Polynomial
namespace ErdosProblems.Erdos1049
variable {R : Type*} [CommRing R]
/-! ## q-Pochhammer and Gaussian binomials -/
def gaussBinom (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0
@[simp] theorem gaussBinom_zero_right (q : R) :
    ∀ n, gaussBinom q n 0 = 1
  | 0 => rfl
  | _n + 1 => rfl
theorem gaussBinom_succ (q : R) (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) =
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0 := rfl
theorem gaussBinom_eq_zero_of_lt (q : R) : ∀ {n k : ℕ}, n < k → gaussBinom q n k = 0
  | 0, 0, h => (Nat.lt_irrefl 0 h).elim
  | 0, k + 1, _ => rfl
  | n + 1, 0, h => (Nat.not_lt_zero _ h).elim
  | n + 1, k + 1, h => by
      have h1 : n < k + 1 := Nat.lt_of_succ_lt_succ (Nat.lt_succ_of_lt h)
      have h2 : ¬ k ≤ n := Nat.not_le.mpr (Nat.lt_of_succ_lt_succ h)
      rw [gaussBinom_succ, gaussBinom_eq_zero_of_lt q h1, if_neg h2, add_zero]
theorem gaussBinom_self (q : R) : ∀ n, gaussBinom q n n = 1
  | 0 => rfl
  | n + 1 => by
      rw [gaussBinom_succ, gaussBinom_eq_zero_of_lt q (Nat.lt_succ_self n),
        if_pos le_rfl, gaussBinom_self q n, Nat.sub_self, pow_zero, one_mul,
        zero_add]
theorem gaussBinom_succ_of_le (q : R) {n j : ℕ} (hj : j ≤ n) :
    gaussBinom q (n + 1) (j + 1) =
      gaussBinom q n (j + 1) + q ^ (n - j) * gaussBinom q n j := by
  rw [gaussBinom_succ, if_pos hj]
theorem choose_two_succ (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
  rw [show (j + 1).choose 2 = j.choose 1 + j.choose 2 from Nat.choose_succ_succ j 1,
    Nat.choose_one_right]
  omega
lemma eval₂_gaussBinom (q : R) : ∀ n k,
    eval₂ (Int.castRingHom R) q (gaussBinom (X : ℤ[X]) n k) = gaussBinom q n k
  | 0, 0 => by simp [gaussBinom]
  | 0, k + 1 => by simp [gaussBinom]
  | n + 1, 0 => by simp [gaussBinom]
  | n + 1, k + 1 => by
      rw [gaussBinom_succ, gaussBinom_succ, eval₂_add]
      split_ifs with h
      · rw [eval₂_mul, eval₂_pow, eval₂_X, eval₂_gaussBinom q n (k + 1),
          eval₂_gaussBinom q n k]
      · rw [eval₂_zero, eval₂_gaussBinom q n (k + 1)]
end ErdosProblems.Erdos1049

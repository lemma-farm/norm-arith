/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module
public import Mathlib
public import Mathlib.Analysis.Real.Sqrt
-- Used only inside proofs.
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The convergents of a continued fraction `[0; a₁, a₂, …]` (Bugeaud 2013, §2)

For a sequence `a₁, a₂, …` of positive integers, the convergents `p_ℓ / q_ℓ = [0; a₁, …, a_ℓ]`
are given by `p₋₁ = q₀ = 1`, `q₋₁ = p₀ = 0` and the recursion (2.1)
`q_ℓ = a_ℓ q_{ℓ-1} + q_{ℓ-2}`, `p_ℓ = a_ℓ p_{ℓ-1} + p_{ℓ-2}`. The paper's `a_ℓ` is `a ℓ`; the
value `a 0` is never used. This file collects the elementary facts of §2 that do not involve the
limit `α = [0; a₁, a₂, …]`.

## Main definitions

* `Nat.contNum a ℓ`, `Nat.contDen a ℓ`: `p_ℓ` and `q_ℓ`, for `ℓ ≥ 0`.
* `List.cfValue l`: the finite continued fraction `[0; b₁, …, b_k]` of a list of naturals.

## Main results

* `Nat.contNum_mul_contDen_sub`: `p_{ℓ+1} q_ℓ - p_ℓ q_{ℓ+1} = (-1)^ℓ`.
* `Nat.coprime_contNum_contDen`, `Nat.coprime_contDen_succ`: `p_ℓ ⊥ q_ℓ` and `q_ℓ ⊥ q_{ℓ+1}`.
* `Nat.contDen_lt_contDen_succ`: `(q_ℓ)_{ℓ ≥ 1}` is increasing; `Nat.contNum_le_contDen`.
* `Nat.contDen_mul_sqrt_two_pow_le`: **(2.3)**, `q_{ℓ+h} ≥ q_ℓ √2^{h-1}`.
* `Nat.contDen_div_contDen_succ`: **the mirror formula (2.4)**,
  `q_{ℓ-1} / q_ℓ = [0; a_ℓ, a_{ℓ-1}, …, a₁]`.

## References

Y. Bugeaud, *Automatic continued fractions are transcendental or quadratic*, Ann. Sci. Éc. Norm.
Supér. (4) **46** (2013), 1005–1022, §2; O. Perron, *Die Lehre von den Kettenbrüchen*, 1929.
-/
@[expose] public section
namespace List
end List
namespace Nat
/-- **The numerators of the convergents** `p_ℓ` of `[0; a₁, a₂, …]`: `p₀ = 0`, `p₁ = 1`,
`p_ℓ = a_ℓ p_{ℓ-1} + p_{ℓ-2}`. -/
def contNum (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => a (n + 2) * contNum a (n + 1) + contNum a n
/-- **The denominators of the convergents** `q_ℓ` of `[0; a₁, a₂, …]`: `q₀ = 1`, `q₁ = a₁`,
`q_ℓ = a_ℓ q_{ℓ-1} + q_{ℓ-2}`. -/
def contDen (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 1
  | n + 2 => a (n + 2) * contDen a (n + 1) + contDen a n
variable {a : ℕ → ℕ}
@[simp] theorem contNum_zero (a : ℕ → ℕ) : contNum a 0 = 0 := rfl
@[simp] theorem contNum_one (a : ℕ → ℕ) : contNum a 1 = 1 := rfl
@[simp] theorem contDen_zero (a : ℕ → ℕ) : contDen a 0 = 1 := rfl
@[simp] theorem contDen_one (a : ℕ → ℕ) : contDen a 1 = a 1 := rfl
/-- **(2.1)** for the numerators. -/
theorem contNum_add_two (a : ℕ → ℕ) (n : ℕ) :
    contNum a (n + 2) = a (n + 2) * contNum a (n + 1) + contNum a n := rfl
/-- **(2.1)** `q_ℓ = a_ℓ q_{ℓ-1} + q_{ℓ-2}`. -/
theorem contDen_add_two (a : ℕ → ℕ) (n : ℕ) :
    contDen a (n + 2) = a (n + 2) * contDen a (n + 1) + contDen a n := rfl
/-- **The determinant of consecutive convergents**: `p_{ℓ+1} q_ℓ - p_ℓ q_{ℓ+1} = (-1)^ℓ`. -/
theorem contNum_mul_contDen_sub (a : ℕ → ℕ) (n : ℕ) :
    (contNum a (n + 1) : ℤ) * contDen a n - contNum a n * contDen a (n + 1) = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [contNum_add_two, contDen_add_two]
    push_cast
    linear_combination -ih
section Positive
/-! The partial quotients are positive integers: `a_ℓ ≥ 1` for `ℓ ≥ 1`. -/
variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha
/-- `q_ℓ ≤ q_{ℓ+1}`. -/
theorem contDen_le_contDen_succ (n : ℕ) : contDen a n ≤ contDen a (n + 1) := by
  rcases n with _ | n
  · simpa using ha 0
  · rw [contDen_add_two]
    have := ha (n + 1)
    nlinarith
/-- `q_ℓ ≥ 1`. -/
theorem one_le_contDen (n : ℕ) : 1 ≤ contDen a n := by
  induction n with
  | zero => simp
  | succ n ih => exact ih.trans (contDen_le_contDen_succ ha n)
theorem contDen_pos (n : ℕ) : 0 < contDen a n := one_le_contDen ha n
end Positive
end Nat

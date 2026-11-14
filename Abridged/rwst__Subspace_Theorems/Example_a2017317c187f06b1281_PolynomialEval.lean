module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.ComputeDegree

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.v7cd0eb29f9ba.DiophantineApproximation.PolynomialSupNorm ====
public section
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
-- Used only inside proofs and in the acceptance criteria.
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The naive height of an integer polynomial

The **naive height** of `P = ∑ aᵢ Xⁱ` is `max |aᵢ|`, and it is the height that Mahler's and
Koksma's exponents are normalized by. Mathlib already has it, under a name that says what it is
rather than what it is used for: `Polynomial.supNorm`, the Gauss norm of the norm of the
coefficient ring at `c = 1`. Nothing is redefined here. What is missing is the API that Layer 1.2
runs on, and it is of two kinds.

The first is arithmetic, and holds over any seminormed ring: subadditivity, the behaviour under
multiplication by a constant, and the invariance under `Polynomial.reflect`, which reverses the
coefficients and so permutes the very set the supremum is taken over.

The second is **Northcott's theorem for integer polynomials**, and it is the reason the exponents
of Layer 1.2 can be defined by an infinite set of solutions and used through a bound on the
height: over `ℤ` a polynomial of bounded degree and bounded naive height lies in a finite set, so
an infinite set of solutions of bounded degree has *unbounded* height, and any constant in front
of `H(P) ^ (-w)` can be absorbed by lowering `w`. Over `ℚ` this fails — `C (1 / n)` has height
`1 / n` — and the failure is exactly the integrality that makes `1 ≤ H(P)` for `P ≠ 0`.

## Main results

* `Polynomial.supNorm_add_le`, `Polynomial.supNorm_sum_le`, `Polynomial.supNorm_C_mul`,
  `Polynomial.supNorm_le_of_forall` and `Polynomial.supNorm_reflect`: the arithmetic of the naive
  height over a seminormed ring. Reflection, which reverses the coefficients, preserves it
  *exactly*.
* `Polynomial.supNorm_linear` and `Polynomial.coeff_linear_zero`, `_one`, `_add_two`: the naive
  height of `a X + b` is `max |a| |b|` — the naive height of the fraction `-b / a` in the sense
  of Layer 1.1.
* `Polynomial.one_le_supNorm` and `Polynomial.supNorm_pos`: over `ℤ`, a nonzero polynomial has
  height at least `1`.
* `Polynomial.finite_setOf_natDegree_le_supNorm_le`: **Northcott for integer polynomials**, the
  finiteness of the polynomials of bounded degree and bounded naive height.
* `Polynomial.infinite_sep_lt_supNorm`: an infinite set of integer polynomials of bounded degree
  still has infinitely many members above any given height, and
  `Polynomial.infinite_of_forall_exists_lt_supNorm`, the converse direction.
* `Polynomial.exists_pos_lt_supNorm_of_abs_aeval_lt` and
  `Polynomial.exists_pos_lt_supNorm_of_abs_sub_root_lt`: **the two height gaps**. Below a
  threshold that depends only on the height bound, a nonzero value at `ξ` — respectively a root
  at positive distance less than the threshold from `ξ` — forces the naive height above that
  bound. Layer 1.2 uses one or the other every time it replaces a solution by another polynomial.
* `Polynomial.supNorm_comp_le` and `Polynomial.one_le_sum_supNorm_pow`: a substitution multiplies
  the naive height by at most a constant depending only on the substituted polynomial and the
  degree bound.

## Implementation notes

⚠ **`Polynomial.supNorm` is the naive height and no wrapper is introduced.** Mathlib's own
module documentation says so ("often called the *(naive) height*") and declines the name because
`Height` is taken; a local abbreviation would only hide `Polynomial.le_supNorm` and
`Polynomial.exists_eq_supNorm`, which are what every proof below uses. The zero polynomial has
height `0`, not the junk value `1` of the projective heights — `supNorm` is a norm, not a height —
and every statement of Layer 1.2 excludes it through `0 < |P ξ|` anyway.

The finiteness proof reads a polynomial of degree at most `n` off its coefficient vector on
`Fin (n + 1)`; that map is injective there, and its image lands in a product of finite intervals
of `ℤ`. The bound on a coefficient is `⌈B⌉`, so the statement is for a real bound and no
integrality of `B` is assumed.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), §3.1. E.
Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.6.

This is part of Layer 1.2 of the `DiophantineApproximation` roadmap.
-/
public section
namespace Polynomial
/-! ### The naive height over a seminormed ring -/
section Seminormed
variable {A : Type*} [SeminormedRing A]

end Seminormed
/-! ### Integrality and Northcott -/
section Integer
variable {P : ℤ[X]}
set_option linter.unusedVariables false in
axiom _root_.Polynomial.abs_coeff_le_supNorm : ∀ (P : Polynomial ℤ) (i : ℕ), |(↑((P.coeff : ℕ → ℤ) i) : ℝ)| ≤ P.supNorm

end Integer
end Polynomial
/-! ### Acceptance criteria -/
section Examples
open Polynomial
end Examples

end
end

-- ==== Examples.rwst__Subspace_Theorems.Examples.Example_a2017317c187f06b1281_PolynomialEval ====
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
-- Used only inside proofs and in the acceptance criteria.
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Archimedean bounds on an integer polynomial

`DiophantineApproximation/PolynomialSupNorm.lean` proved everything Layer 1.2 needed about the
naive height `Polynomial.supNorm`, and never had to evaluate a polynomial anywhere: the value
`aeval ξ P` entered its statements only through the hypothesis that it is small. Layer 1.3 has to
*produce* small values, and for that the trivial upper bound on an evaluation and its mean value
form are the two steps every argument begins with:

```text
|P x|  ≤ (n + 1) * H(P) * max 1 |x| ^ n,
|P y - P x| ≤ (n + 1) ^ 2 * H(P) * max 1 (max |x| |y|) ^ n * |y - x|.
```

Both are stated with `n` a bound on the degree rather than the degree itself, because that is how
every consumer has them — the degree of a solution varies inside a set of solutions, the bound
does not — and both carry the factor `max 1 |x| ^ n`, without which they are false.

## Main results

* `Polynomial.abs_aeval_le`: the triangle inequality for an evaluation.
* `Polynomial.supNorm_derivative_le`: differentiating multiplies the naive height by at most
  `n + 1`.
* `Polynomial.abs_aeval_derivative_le`: the two combined, the bound Layer 1.3 uses on `P'`.
* `Polynomial.abs_aeval_sub_aeval_le`: **the mean value theorem for an integer polynomial**, with
  a constant that depends only on the degree bound, the naive height and the interval.

## Implementation notes

⚠ **The derivative is bounded by `n + 1`, not by `n`.** The sharp factor is `n`, from
`(derivative P).coeff i = (i + 1) * P.coeff (i + 1)` with `i + 1 ≤ n`; the sharp form is useless
here because it degenerates at `n = 0`, where every constant a consumer builds out of it — and
every consumer builds one — would be zero. `n + 1` keeps the constants positive at every degree
bound, which is what `Real.le_mahlerExponent_of_infinite` asks for.

⚠ **The mean value theorem is `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on
`Set.uIcc`.** Nothing is assumed about the order of `x` and `y`, so the interval has to be the
unordered one; `Set.uIcc` is convex and contains both endpoints, and those three facts are the
whole interface. The alternative — the algebraic identity `x ^ k - y ^ k = (x - y) * ∑ …` summed
against the coefficients — proves the same bound with no analysis at all, and is longer.

⚠ **`aeval` over `ℤ` and `eval` over `ℝ` have to be reconciled once.** Mathlib's derivative API is
about `eval` on `ℝ[X]`, the naive height is about `ℤ[X]`, and `Polynomial.derivative_map` is what
lets the two be used in the same calculation; the map is applied to `P`, never to the height.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Appendix A.

This is part of Layer 1.3 of the `DiophantineApproximation` roadmap.
-/
public section
namespace Polynomial
variable {P : ℤ[X]} {n : ℕ}
/-! ### The value and the derivative at a real point -/

set_option linter.unusedVariables false in
/-- **Differentiating multiplies the naive height by at most `n + 1`.** -/
theorem supNorm_derivative_le (hP : P.natDegree ≤ n) 
    (h_Polynomial_supNorm_le_of_forall : ∀ {A : Type} [inst : SeminormedRing A] {P : Polynomial A} {c : ℝ},
      (∀ (i : ℕ), ‖(P.coeff : ℕ → A) i‖ ≤ c) → P.supNorm ≤ c)
    :
    (derivative P).supNorm ≤ ((n : ℝ) + 1) * P.supNorm := by
  refine h_Polynomial_supNorm_le_of_forall fun i ↦ ?_
  have hi0 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
  rw [Int.norm_eq_abs, coeff_derivative]
  push_cast
  rw [abs_mul, abs_of_nonneg hi0]
  rcases le_or_gt (i + 1) n with h | h
  · have h1 : |((P.coeff (i + 1) : ℤ) : ℝ)| ≤ P.supNorm := P.abs_coeff_le_supNorm _
    have h2 : (i : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_succ_le h
      linarith
    calc |((P.coeff (i + 1) : ℤ) : ℝ)| * ((i : ℝ) + 1)
        ≤ P.supNorm * ((n : ℝ) + 1) := by
          exact mul_le_mul h1 h2 hi0 P.supNorm_nonneg
      _ = ((n : ℝ) + 1) * P.supNorm := by ring
  · have hz : P.coeff (i + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz]
    simpa using mul_nonneg (by positivity) P.supNorm_nonneg

/-! ### The mean value theorem -/

/-! ### Acceptance criteria -/
end Polynomial

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

-- ==== Examples.rwst__Subspace_Theorems.Examples.Example_8d5d7d6d545b3ec1c982_PolynomialEval ====
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

/-! ### The mean value theorem -/

set_option linter.unusedVariables false in
/-- **The mean value theorem for an integer polynomial.** The increment of `P` between two real
points is at most `(n + 1) ^ 2 * H(P) * max 1 (max |x| |y|) ^ n` times their distance. This is
the step that turns "`α` is a root of `P` near `ξ`" into "`P` is small at `ξ`", which is the whole
of `Real.koksmaExponent_le_mahlerExponent`. -/
theorem abs_aeval_sub_aeval_le (hP : P.natDegree ≤ n) (x y : ℝ) 
    (h_Polynomial_abs_le_max_abs_of_mem_uIcc : ∀ {x y z : ℝ}, z ∈ Set.uIcc x y → |z| ≤ Max.max |x| |y|)
    (h_Polynomial_abs_aeval_derivative_le : ∀ {P : Polynomial ℤ} {n : ℕ},
      P.natDegree ≤ n →
        ∀ (x : ℝ),
          |(Polynomial.aeval x : Polynomial ℤ → ℝ)
                ((Polynomial.derivative : Polynomial ℤ → Polynomial ℤ) P)| ≤
            ((↑n : ℝ) + 1) ^ 2 * (P.supNorm * Max.max 1 |x| ^ n))
    :
    |aeval y P - aeval x P|
      ≤ ((n : ℝ) + 1) ^ 2 * (P.supNorm * max 1 (max |x| |y|) ^ n) * |y - x| := by
  set M : ℝ := max 1 (max |x| |y|) with hM
  set Q : ℝ[X] := P.map (Int.castRingHom ℝ) with hQdef
  have hev : ∀ z : ℝ, aeval z P = eval z Q := by
    intro z
    rw [hQdef, aeval_def, eval₂_eq_eval_map]
    rfl
  have hdev : ∀ z : ℝ, eval z (derivative Q) = aeval z (derivative P) := by
    intro z
    rw [hQdef, derivative_map, aeval_def, eval₂_eq_eval_map]
    rfl
  have hderiv : ∀ z ∈ Set.uIcc x y,
      HasDerivWithinAt (fun z ↦ eval z Q) (eval z (derivative Q)) (Set.uIcc x y) z :=
    fun z _ ↦ (Q.hasDerivAt z).hasDerivWithinAt
  have hbnd : ∀ z ∈ Set.uIcc x y,
      ‖eval z (derivative Q)‖ ≤ ((n : ℝ) + 1) ^ 2 * (P.supNorm * M ^ n) := by
    intro z hz
    rw [Real.norm_eq_abs, hdev z]
    refine (h_Polynomial_abs_aeval_derivative_le hP z).trans ?_
    have hle : max 1 |z| ≤ M := max_le_max le_rfl (h_Polynomial_abs_le_max_abs_of_mem_uIcc hz)
    have h1 : (0 : ℝ) ≤ max 1 |z| := le_trans zero_le_one (le_max_left _ _)
    gcongr
    exact P.supNorm_nonneg
  have hkey := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbnd
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← hev x, ← hev y] at hkey
  exact hkey
/-! ### Acceptance criteria -/
end Polynomial

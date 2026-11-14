module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic
public import Mathlib.Analysis.Normed.Group.AddCircle

-- ==== Examples.nihargargava__systole_bound.Dependencies.v9002dcf8fb98.CookMagyar.CircleMethod ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.

The additive-character and interval-orthogonality proofs in this file are
adapted from Gershon Bialer's `ternary-goldbach-lean`,
`MathExtras.NumberTheory.Vinogradov.CircleMethod` (Apache-2.0).  The
arbitrary-arity cubic coefficient extraction is new to this project.
-/
@[expose] public section
open MeasureTheory
open scoped ArithmeticFunction BigOperators
namespace SystolicGrowth
/-! # Exact circle-method identities for `x^3 - x`

This file contains the algebraic and Fourier-analytic part of the
Cook--Magyar specialization.  There are no asymptotic estimates here: the
main result, `integral_cubicVonMangoldtExpSum_pow`, is the exact identity
which turns a Fourier integral into the von-Mangoldt-weighted number of
representations of a target by `n` values of `x^3-x`.
-/
/-- The cubic polynomial used throughout the arithmetic construction. -/
def primeCubic (x : ℕ) : ℕ := x ^ 3 - x
namespace CookMagyarCircle
/-- The additive character `e(kα) = exp(2πikα)`. -/
noncomputable def addChar (α : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (α : ℂ))
/-- The negative-frequency character `e(-kα)`. -/
noncomputable def negAddChar (α : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ))

/-- The cubic von-Mangoldt exponential sum at scale `N`.  The indexing type
`Fin (N+1)` represents the closed interval `0 ≤ x ≤ N`. -/
noncomputable def cubicVonMangoldtExpSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ x : Fin (N + 1),
    (ArithmeticFunction.vonMangoldt x : ℂ) * addChar α (primeCubic x)
/-- The real von-Mangoldt weight of a tuple. -/
noncomputable def tupleVonMangoldtWeight {n N : ℕ}
    (x : Fin n → Fin (N + 1)) : ℝ :=
  ∏ i, ArithmeticFunction.vonMangoldt (x i)
/-- Weighted number of representations
`T = Σ_i (x_i^3-x_i)` with `0 ≤ x_i ≤ N`. -/
noncomputable def cubicVonMangoldtRepresentation
    (n N T : ℕ) : ℝ :=
  ∑ x : Fin n → Fin (N + 1),
    if (∑ i, primeCubic (x i)) = T then tupleVonMangoldtWeight x else 0

end CookMagyarCircle
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Dependencies.v9002dcf8fb98.CookMagyar.Arcs ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.

The elementary major/minor-arc decomposition in this file is adapted from
Gershon Bialer's `ternary-goldbach-lean`, in particular
`MathExtras.NumberTheory.Vinogradov.CircleMethod` and
`Math.Problems.TernaryGoldbach.CircleMethodDecomposition.Core`
(Apache-2.0).  The cubic scaling and arbitrary-power integrand are specific
to the Cook--Magyar specialization developed here.
-/
@[expose] public section
open MeasureTheory
namespace SystolicGrowth
namespace CookMagyarArcs
open CookMagyarCircle
/-! # Major and minor arcs for the cubic Cook--Magyar sum

For a cutoff `Q`, the major-arc centers are the reduced fractions `a / q`
with `0 <= a < q <= Q`.  At cubic scale `N`, each arc has radius
`Q / N^3`, as in the one-equation specialization of Cook--Magyar.  All arcs
are clipped to the fixed fundamental interval `[0, 1]`; the minor arcs are
the relative complement there.

This file only establishes the exact decomposition and its elementary
analytic prerequisites.  Estimates on the two pieces belong in subsequent
modules.
-/
/-- Reduced rational centers `a / q` with denominator at most `Q`.

The pair convention is `(numerator, denominator)`. -/
def majorArcCenters (Q : ℕ) : Set (ℕ × ℕ) :=
  {aq | aq.2 ≤ Q ∧ aq.2 ≠ 0 ∧ aq.1 < aq.2 ∧ Nat.Coprime aq.1 aq.2}
/-- The rational number represented by a major-arc center. -/
noncomputable def rationalCenter (a q : ℕ) : ℝ :=
  (a : ℝ) / (q : ℝ)
/-- The cubic major-arc radius.  Analytic applications take `Q` to be a
power of `log N`. -/
noncomputable def cubicArcRadius (N Q : ℕ) : ℝ :=
  (Q : ℝ) / (N : ℝ) ^ 3
/-- Distance modulo the period `1`.  Using the circle distance, rather than
ordinary distance in `ℝ`, is essential at the identified endpoints `0` and
`1` of the chosen fundamental interval. -/
noncomputable def periodicDistance (α β : ℝ) : ℝ :=
  dist (α : UnitAddCircle) (β : UnitAddCircle)
/-- The major arcs in the chosen fundamental interval `[0, 1]`. -/
noncomputable def majorArcs (N Q : ℕ) : Set ℝ :=
  {α | α ∈ Set.Icc (0 : ℝ) 1 ∧
    ∃ a q : ℕ, (a, q) ∈ majorArcCenters Q ∧
      periodicDistance α (rationalCenter a q) < cubicArcRadius N Q}
/-- The minor arcs are the relative complement of the major arcs in
`[0, 1]`. -/
noncomputable def minorArcs (N Q : ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 \ majorArcs N Q

/-! ## The cubic Fourier integrand -/
/-- The Fourier integrand whose full-period integral extracts the target
coefficient for `n` copies of `x^3 - x`. -/
noncomputable def cubicIntegrand (n N T : ℕ) (α : ℝ) : ℂ :=
  (cubicVonMangoldtExpSum α N) ^ n * negAddChar α T

/-- The major-arc contribution to the cubic Fourier coefficient. -/
noncomputable def cubicMajorArcIntegral (n N T Q : ℕ) : ℂ :=
  ∫ α in majorArcs N Q, cubicIntegrand n N T α
/-- The minor-arc contribution to the cubic Fourier coefficient. -/
noncomputable def cubicMinorArcIntegral (n N T Q : ℕ) : ℂ :=
  ∫ α in minorArcs N Q, cubicIntegrand n N T α

end CookMagyarArcs
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Examples.Example_7bd8a756907fece0c1b1_Assembly ====
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
@[expose] public section
namespace SystolicGrowth
namespace CookMagyarCircle
open CookMagyarArcs
/-! # Quantitative assembly of the cubic circle method

This file contains the last purely formal implication in the circle-method
argument.  The full weighted coefficient is split into its major- and
minor-arc pieces.  If the major arcs approximate a positive real main term,
the minor arcs are small, and the tuples containing a prime power (or the
prime `2`) are smaller still, then the odd-prime part of the coefficient is
positive.

No number-theoretic estimate is assumed implicitly by these results: all
three error bounds occur explicitly in the hypotheses.  Later analytic
modules can therefore be audited independently and then combined here.
-/
set_option linter.unusedVariables false in
/-- A norm bound for the two arc pieces gives a lower bound for the real
weighted representation count. -/
theorem cubicVonMangoldtRepresentation_lower_of_arc_bounds
    {n N T Q : ℕ} {mainTerm majorError minorError : ℝ}
    (hmajor :
      ‖cubicMajorArcIntegral n N T Q - (mainTerm : ℂ)‖ ≤ majorError)
    (hminor : ‖cubicMinorArcIntegral n N T Q‖ ≤ minorError) 
    (h_SystolicGrowth_CookMagyarArcs_cubicVonMangoldtRepresentation_eq_major_add_minor : ∀ (n N T Q : ℕ),
      (↑(SystolicGrowth.CookMagyarCircle.cubicVonMangoldtRepresentation n N T) : ℂ) =
        SystolicGrowth.CookMagyarArcs.cubicMajorArcIntegral n N T Q +
          SystolicGrowth.CookMagyarArcs.cubicMinorArcIntegral n N T Q)
    :
    mainTerm - (majorError + minorError) ≤
      cubicVonMangoldtRepresentation n N T := by
  have hdecomp :=
    h_SystolicGrowth_CookMagyarArcs_cubicVonMangoldtRepresentation_eq_major_add_minor n N T Q
  have hnorm :
      ‖(cubicVonMangoldtRepresentation n N T : ℂ) - (mainTerm : ℂ)‖ ≤
        majorError + minorError := by
    calc
      ‖(cubicVonMangoldtRepresentation n N T : ℂ) - (mainTerm : ℂ)‖ =
          ‖(cubicMajorArcIntegral n N T Q - (mainTerm : ℂ) +
            cubicMinorArcIntegral n N T Q)‖ := by rw [hdecomp]; ring_nf
      _ ≤ ‖cubicMajorArcIntegral n N T Q - (mainTerm : ℂ)‖ +
          ‖cubicMinorArcIntegral n N T Q‖ := norm_add_le _ _
      _ ≤ majorError + minorError := add_le_add hmajor hminor
  have habs :
      |cubicVonMangoldtRepresentation n N T - mainTerm| ≤
        majorError + minorError := by
    have hcast :
        (cubicVonMangoldtRepresentation n N T : ℂ) - (mainTerm : ℂ) =
          ((cubicVonMangoldtRepresentation n N T - mainTerm : ℝ) : ℂ) := by
      exact (map_sub Complex.ofRealHom _ _).symm
    rw [hcast, Complex.norm_real] at hnorm
    exact hnorm
  have hlower :
      -(majorError + minorError) ≤
        cubicVonMangoldtRepresentation n N T - mainTerm :=
    (neg_le_neg habs).trans
      (neg_abs_le (cubicVonMangoldtRepresentation n N T - mainTerm))
  linarith

end CookMagyarCircle
end SystolicGrowth

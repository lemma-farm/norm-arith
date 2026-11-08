module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v9002dcf8fb98.CookMagyar.Arcs
public import Examples.nihargargava__systole_bound.Dependencies.v9002dcf8fb98.CookMagyar.PrimePowerRemoval
public import Examples.nihargargava__systole_bound.Dependencies.v9002dcf8fb98.CookMagyar.Scale
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
/-- A norm bound for the two arc pieces gives a lower bound for the real
weighted representation count. -/
theorem cubicVonMangoldtRepresentation_lower_of_arc_bounds
    {n N T Q : ℕ} {mainTerm majorError minorError : ℝ}
    (hmajor :
      ‖cubicMajorArcIntegral n N T Q - (mainTerm : ℂ)‖ ≤ majorError)
    (hminor : ‖cubicMinorArcIntegral n N T Q‖ ≤ minorError) :
    mainTerm - (majorError + minorError) ≤
      cubicVonMangoldtRepresentation n N T := by
  have hdecomp :=
    cubicVonMangoldtRepresentation_eq_major_add_minor n N T Q
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
/-- The three quantitative estimates needed to extract an odd-prime
solution at fixed `n`, `N`, and `T`. -/
structure CubicCircleBounds (n N T : ℕ) where
  /-- Denominator cutoff defining the major arcs. -/
  cutoff : ℕ
  /-- The real singular-series times singular-integral main term. -/
  mainTerm : ℝ
  majorError : ℝ
  minorError : ℝ
  discardedError : ℝ
  major_bound :
    ‖cubicMajorArcIntegral n N T cutoff - (mainTerm : ℂ)‖ ≤ majorError
  minor_bound :
    ‖cubicMinorArcIntegral n N T cutoff‖ ≤ minorError
  discarded_bound :
    cubicDiscardedRepresentation n N T ≤ discardedError
  /-- The positive main term strictly dominates all errors. -/
  dominates : majorError + minorError + discardedError < mainTerm
end CookMagyarCircle
end SystolicGrowth

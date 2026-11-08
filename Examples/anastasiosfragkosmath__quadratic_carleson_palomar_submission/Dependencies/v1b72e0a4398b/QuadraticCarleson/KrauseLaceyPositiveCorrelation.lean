/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyDyadicLocalization
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.QuadraticFixedHeightAveragingCorrelation
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.QuadraticFixedHeightAveragingSigned
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The degree-two positive-half correlation in Krause--Lacey

This module proves the degree-two specialization of the oscillatory kernel
estimate (2.4) used at the start of the proof of Krause--Lacey Lemma 3.5.
For the positive-half kernel `ψₖ(y) = e(y²) ρₖ⁺(y)`, its `TT*`
correlation is `O(R⁻¹)` in a fixed neighborhood of the diagonal,
`O(R⁻²)` away from that neighborhood, and vanishes outside a constant
multiple of the annular radius `R`.

The off-diagonal gain is obtained from the project's proved quadratic
integration-by-parts theorem.  When the two modulations are both one, the
quadratic term in the `TT*` phase cancels and its slope is the constant
`4π(y-x)`.  No local `L¹ → L^q` estimate or sparse bound is assumed here.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate Interval
namespace QuadraticCarleson
set_option autoImplicit false
theorem krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution
    (j : ℤ) (I : RealInterval) (f : ℝ → ℂ) (x : ℝ) :
    krauseLaceyLocalizedPiece 1 j I f x =
      ∫ t, annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) *
        I.centralThird.indicator f t := by
  let F : ℝ → ℂ := fun t ↦
    annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) *
      I.centralThird.indicator f t
  unfold krauseLaceyLocalizedPiece
  calc
    (∫ y, positiveDyadicAmplitude j y * phase (1 * y ^ 2) *
        I.centralThird.indicator f (x - y)) = ∫ y, F (x - y) := by
      apply integral_congr_ae
      filter_upwards with y
      have hxy : x - (x - y) = y := by ring
      simp only [F, annularQuadraticKernel, one_mul]
      rw [hxy]
    _ = ∫ t, F t := MeasureTheory.integral_sub_left_eq_self F volume x
    _ = _ := rfl
end QuadraticCarleson

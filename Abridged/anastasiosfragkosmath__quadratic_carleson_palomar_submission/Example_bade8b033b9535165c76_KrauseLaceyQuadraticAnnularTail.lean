import Mathlib
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.ve3c1b520e9eb.QuadraticCarleson.QuadraticCenteredMaximal ====
section
/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# One-dimensional centered maximal estimates

The fixed-height quadratic `TT*` argument uses a one-dimensional centered
maximal estimate. The covering argument below proves the needed weak estimate
directly from Mathlib's Vitali theorem, with an explicit constant.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace QuadraticCarleson

/-- The centered interval average, allowing nonnegative extended-valued input. -/
noncomputable def centeredAverage (r : ℝ) (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in closedBall x r, f y) / ENNReal.ofReal (2 * r)

end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.ve3c1b520e9eb.QuadraticCarleson.HardyLittlewoodMaximal ====
section
/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The centered Hardy--Littlewood maximal operator on the real line

We use positive rational radii.  This makes the pointwise supremum measurably
countable while retaining arbitrarily small and arbitrarily large intervals.
The weak `(1,1)` estimate is obtained from the bounded-radius Vitali estimate
in `QuadraticCenteredMaximal` and continuity of measure from below.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace QuadraticCarleson
/-- Positive rational radii, used as a countable cofinal family. -/
abbrev PositiveRational := {q : ℚ // 0 < q}

/-- The centered maximal operator over all positive rational radii. -/
noncomputable def centeredHardyLittlewoodMaximal (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q : PositiveRational, centeredAverage (q : ℝ) f x

end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Examples.Example_bade8b033b9535165c76_KrauseLaceyQuadraticAnnularTail ====
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Maximal tails of separated quadratic frequency pieces

This file isolates the frequency-projection part of the direct quadratic
one-node argument.  A finite tail is written as the total sum minus a
prefix.  If every prefix is a smooth low-pass projection of the total sum,
and the low-pass kernels are pointwise dominated by a fixed multiple of the
centered Hardy--Littlewood maximal function, then the whole family of tails
has a cardinality-free `L²` bound.

The application-specific input may be supplied either pointwise through
`HasLowPassPrefixControl` or almost everywhere through
`HasAELowPassPrefixControl`.  The latter is the natural interface for `L²`
Fourier multipliers.  No maximal-tail theorem or orthogonality principle is
assumed here.
-/
open Function MeasureTheory Set FourierTransform Metric
open scoped ENNReal NNReal ComplexConjugate
namespace QuadraticCarleson.KrauseLaceyQuadraticAnnularTail
set_option autoImplicit false
noncomputable section
/-- The pointwise total of a finite sequence of frequency pieces. -/
def finitePieceTotal (N : ℕ) (u : ℕ → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N, u j x
/-- The prefix strictly below `n`. -/
def finitePiecePrefix (u : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, u j x
/-- The finite tail beginning at `n`, represented as total minus prefix.
For `n ≤ N` this is exactly `∑_{n ≤ j < N} u_j`. -/
def finitePieceTail (N : ℕ) (u : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  finitePieceTotal N u x - finitePiecePrefix u n x
/-- The maximum of the tails beginning at `0, ..., N`. -/
def finitePieceTailMax (N : ℕ) (u : ℕ → ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  (Finset.range (N + 1)).sup fun n ↦ ‖finitePieceTail N u n x‖ₑ

/-- The measure-theoretically natural version of low-pass prefix control.
Fourier multiplier identities in `L²` determine representatives only almost
everywhere, and this is sufficient for every subsequent `lintegral` estimate. -/
def HasAELowPassPrefixControl (N : ℕ) (u : ℕ → ℝ → ℂ) (A : ℝ≥0∞) : Prop :=
  ∀ n ≤ N, ∀ᵐ x : ℝ ∂volume,
    ‖finitePiecePrefix u n x‖ₑ ≤
      A * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x


set_option linter.unusedVariables false in
/-- Cardinality-free maximal-tail `L²` estimate from almost-everywhere
low-pass prefix control.  This is the form used by Fourier multiplier
applications, whose canonical representatives agree only almost everywhere. -/
theorem finitePieceTailMax_sq_lintegral_le_ae
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hu : ∀ j, Measurable (u j))
    (hprefix : HasAELowPassPrefixControl N u A) 
    (h_QuadraticCarleson_KrauseLaceyQuadraticAnnularTail_measurable_finitePieceTotal : ∀ {N : ℕ} {u : ℕ → ℝ → ℂ},
      (∀ j < N, Measurable (u j)) →
        Measurable (QuadraticCarleson.KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u))
    (h_QuadraticCarleson_measurable_centeredHardyLittlewoodMaximal : ∀ {f : ℝ → ENNReal}, Measurable f → Measurable (QuadraticCarleson.centeredHardyLittlewoodMaximal f))
    (h_QuadraticCarleson_KrauseLaceyQuadraticAnnularTail_finitePieceTailMax_le_total_add_maximal_ae : ∀ {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ENNReal},
      QuadraticCarleson.KrauseLaceyQuadraticAnnularTail.HasAELowPassPrefixControl N u A →
        ∀ᵐ (x : ℝ),
          QuadraticCarleson.KrauseLaceyQuadraticAnnularTail.finitePieceTailMax N u x ≤
            ‖QuadraticCarleson.KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u x‖ₑ +
              A *
                QuadraticCarleson.centeredHardyLittlewoodMaximal
                  (fun (y : ℝ) ↦
                    ‖QuadraticCarleson.KrauseLaceyQuadraticAnnularTail.finitePieceTotal N u y‖ₑ)
                  x)
    (h_QuadraticCarleson_KrauseLaceyQuadraticAnnularTail_ennreal_add_sq_le_four_sum_sq : ∀ (a b : ENNReal), (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2))
    (h_QuadraticCarleson_centeredHardyLittlewoodMaximal_sq_lintegral_le : ∀ {f : ℝ → ENNReal},
      Measurable f →
        ∫⁻ (x : ℝ), QuadraticCarleson.centeredHardyLittlewoodMaximal f x ^ 2 ≤ 32 * ∫⁻ (x : ℝ), f x ^ 2)
    :
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
      (4 + 128 * A ^ 2) *
        ∫⁻ x, ‖finitePieceTotal N u x‖ₑ ^ 2 := by
  let F : ℝ → ℝ≥0∞ := fun x ↦ ‖finitePieceTotal N u x‖ₑ
  let M : ℝ → ℝ≥0∞ := centeredHardyLittlewoodMaximal F
  have hF : Measurable F :=
    (h_QuadraticCarleson_KrauseLaceyQuadraticAnnularTail_measurable_finitePieceTotal fun j _ ↦ hu j).enorm
  have hpoint : ∀ᵐ x : ℝ ∂volume,
      finitePieceTailMax N u x ^ 2 ≤
        4 * (F x ^ 2 + (A * M x) ^ 2) := by
    filter_upwards [h_QuadraticCarleson_KrauseLaceyQuadraticAnnularTail_finitePieceTailMax_le_total_add_maximal_ae hprefix] with x hx
    exact (pow_le_pow_left' hx 2).trans
      (h_QuadraticCarleson_KrauseLaceyQuadraticAnnularTail_ennreal_add_sq_le_four_sum_sq (F x) (A * M x))
  calc
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
        ∫⁻ x, 4 * (F x ^ 2 + (A * M x) ^ 2) :=
      lintegral_mono_ae hpoint
    _ = 4 * ((∫⁻ x, F x ^ 2) + A ^ 2 * ∫⁻ x, M x ^ 2) := by
      simp_rw [mul_pow]
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_left (hF.pow_const 2)]
      rw [lintegral_const_mul'' (A ^ 2)
        ((h_QuadraticCarleson_measurable_centeredHardyLittlewoodMaximal hF).pow_const 2).aemeasurable]
    _ ≤ 4 * ((∫⁻ x, F x ^ 2) + A ^ 2 * (32 * ∫⁻ x, F x ^ 2)) := by
      gcongr
      exact h_QuadraticCarleson_centeredHardyLittlewoodMaximal_sq_lintegral_le hF
    _ = (4 + 128 * A ^ 2) * ∫⁻ x, F x ^ 2 := by ring
end
end QuadraticCarleson.KrauseLaceyQuadraticAnnularTail

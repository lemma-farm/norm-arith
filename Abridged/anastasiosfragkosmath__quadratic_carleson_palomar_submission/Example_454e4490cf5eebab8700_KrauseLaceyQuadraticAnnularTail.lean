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

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Examples.Example_454e4490cf5eebab8700_KrauseLaceyQuadraticAnnularTail ====
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
/-- The exact pointwise input supplied by smooth low-pass projections.
The constant is in `ℝ≥0∞` so it composes directly with the project's
maximal-function estimate. -/
def HasLowPassPrefixControl (N : ℕ) (u : ℕ → ℝ → ℂ) (A : ℝ≥0∞) : Prop :=
  ∀ n ≤ N, ∀ x,
    ‖finitePiecePrefix u n x‖ₑ ≤
      A * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x


theorem finitePieceTailMax_le_total_add_maximal
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hprefix : HasLowPassPrefixControl N u A) (x : ℝ) :
    finitePieceTailMax N u x ≤
      ‖finitePieceTotal N u x‖ₑ +
        A * centeredHardyLittlewoodMaximal
          (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x := by
  apply Finset.sup_le
  intro n hn
  have hnN : n ≤ N := by
    simpa only [Finset.mem_range] using Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  exact enorm_sub_le.trans
    (add_le_add le_rfl (hprefix n hnN x))

end
end QuadraticCarleson.KrauseLaceyQuadraticAnnularTail

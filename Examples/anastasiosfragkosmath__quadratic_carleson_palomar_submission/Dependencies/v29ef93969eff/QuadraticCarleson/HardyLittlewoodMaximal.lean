/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v29ef93969eff.QuadraticCarleson.QuadraticCenteredMaximal
import Mathlib
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
noncomputable def centeredHardyLittlewoodMaximal (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q : PositiveRational, centeredAverage (q : ℝ) f x
end QuadraticCarleson

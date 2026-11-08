/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.ve3c1b520e9eb.QuadraticCarleson.QuadraticL2Decay
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Uniform quadratic correlation estimates

This file proves the direct quadratic cancellation estimates and the two-region
whole-line kernel majorant (6.7) in the `c = 2` specialization of Lemma 6.2 of
arXiv:2412.15766, for smooth amplitudes on same-sign annular overlaps. Both
comparable and separated scales are included. The final theorems use the
paper's exact `2π` exponential normalization and give an explicit dyadic
decay specialization. The maximal L² operator estimate still requires the
linearization, `TT*` representation, and maximal-function argument.
-/
open MeasureTheory Set
open scoped Interval
namespace QuadraticCarleson
end QuadraticCarleson

/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.ve3c1b520e9eb.QuadraticCarleson.Bohr
import Mathlib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Quadratic analytic inputs for fixed-height L² decay

These are prerequisites for the direct `c = 2` specialization of the proof of
Lemma 6.2 of arXiv:2412.15766, specifically its phase in (6.6) and exceptional
set in (6.8). The resulting genuine real-parameter maximal L² estimate is proved
in `QuadraticFixedHeightAveragingNorm`, with L² stability and a Lipschitz operator
form in `QuadraticFixedHeightL2Stability`.
-/
open MeasureTheory Set
open scoped Interval
namespace QuadraticCarleson
end QuadraticCarleson

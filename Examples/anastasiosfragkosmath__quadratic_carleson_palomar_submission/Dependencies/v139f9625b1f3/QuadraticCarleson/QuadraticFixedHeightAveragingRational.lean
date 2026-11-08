/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.QuadraticFixedHeightAveragingContinuity
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Rational reduction without crossing scale-selection jumps

We parametrize each modulation band by the positive square root of the
absolute modulation. Rational roots strictly inside that band yield rational
nonzero modulations of either sign. Fixed-scale continuity then extends their
bound to the lower endpoint of the half-open band as well.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace QuadraticCarleson
end QuadraticCarleson

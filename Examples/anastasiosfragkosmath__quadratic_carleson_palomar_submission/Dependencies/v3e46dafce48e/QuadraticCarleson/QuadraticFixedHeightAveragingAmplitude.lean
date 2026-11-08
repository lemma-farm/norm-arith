/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.PositiveDyadicKernel
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.QuadraticFixedHeightAveragingCorrelation
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Concrete one-sided dyadic amplitudes for fixed-height quadratic decay

The positive half of the paper's annular dyadic kernel is a dilation of one
fixed smooth compactly supported function. Uniform amplitude and derivative
constants are derived from that fixed function, not supplied as assumptions.
-/
open MeasureTheory Set
open scoped ENNReal NNReal ContDiff
namespace QuadraticCarleson
end QuadraticCarleson

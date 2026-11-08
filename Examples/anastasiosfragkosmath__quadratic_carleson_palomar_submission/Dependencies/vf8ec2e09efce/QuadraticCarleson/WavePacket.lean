/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.Definitions
import Mathlib.Analysis.Calculus.BumpFunction.Normed
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The normalized wave packet used in the negative endpoint construction

Section 3 fixes an even, nonnegative, smooth function supported in
`[-1/4, 1/4]` and having integral one. Mathlib's normalized smooth bump
provides this function directly.
-/
open Function MeasureTheory Metric Set
open scoped ContDiff
namespace QuadraticCarleson
end QuadraticCarleson

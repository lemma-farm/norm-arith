/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.QuadraticFixedHeightAveragingReal
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Conventional exponential L²-norm form

This file repackages the already proved maximal second-moment estimate as
`‖M_h f‖₂ ≤ C 2^(-h/10) ‖f‖₂`, with a positive absolute constant and no
restriction on the real modulation parameter.
-/
open MeasureTheory Set
open scoped ENNReal NNReal
namespace QuadraticCarleson
end QuadraticCarleson

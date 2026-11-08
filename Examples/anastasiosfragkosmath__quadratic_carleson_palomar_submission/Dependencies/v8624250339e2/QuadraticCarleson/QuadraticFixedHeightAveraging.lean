/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.QuadraticL2AdjointTransfer
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Averaging the concrete fixed-height quadratic correlation majorant

The proved oscillatory estimate has height `B / S` on a diagonal strip of
width `u * S`, and height `8403968 * B * u / S` elsewhere in a strip of
width `2 * S`. Each term is a centered averaging kernel times a constant
proportional to `u`. This file makes that conversion and the finite maximal
linearization explicit.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace QuadraticCarleson
end QuadraticCarleson

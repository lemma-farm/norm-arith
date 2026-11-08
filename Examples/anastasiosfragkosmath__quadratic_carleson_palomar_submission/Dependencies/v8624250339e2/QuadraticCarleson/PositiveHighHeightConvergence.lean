/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.PositiveHighHeightTail
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Genuine convergence of the high complex series

The measurable majorant is finite almost everywhere for every L² input.
Outside one null set, the strict high-height series converges absolutely for
every real modulation simultaneously. Thus the tail definitions do not rely
on the default value of a nonsummable complex `tsum`.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveHighHeightEstimate
end PositiveHighHeightEstimate
end QuadraticCarleson

/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.PositiveHighHeightEstimate
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The paper's strict high-height tail

The height parametrization `B + n + 1` is exactly `r > B`. The maximal tail
is bounded by a measurable sum of the actual fixed-height maximal functions,
whose L² norms form a geometric series with ratio `2^(-1/10)`.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveHighHeightEstimate
end PositiveHighHeightEstimate
end QuadraticCarleson

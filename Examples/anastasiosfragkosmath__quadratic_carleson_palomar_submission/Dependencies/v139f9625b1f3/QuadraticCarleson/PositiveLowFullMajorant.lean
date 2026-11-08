/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.LowKernelRealMaximal
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveHighHeightFullEndpoint
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# A common measurable majorant for the full low contribution

The atomwise majorant is cut off on the complement of the triple interval.
Its countable sum is measurable, unlike an arbitrary uncountable supremum.
The paper's exceptional set uses the larger fivefold intervals.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveLowFullEstimate
open CalderonZygmundLevelAtoms LowKernelLevelSummation
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate
end PositiveLowFullEstimate
end QuadraticCarleson

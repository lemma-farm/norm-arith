/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryLowSupport
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryVerySmallRange
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CanonicalScaleAtoms
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleRangeSummation
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositiveLowFullEndpoint
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The genuine lacunary very-small low-kernel contribution

This file combines the cancellation estimate for an actual magnitude-level
atom with the compact support of the paper's telescoped low kernel.  It is the
analytic step which produces the factor
`2^(B + m/2) * length(I)` before the geometric summation in
`LacunaryVerySmallRange`.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace LacunaryVerySmallOperator
open CalderonZygmundLevelAtoms LacunaryLowSupport
open LowKernelLevelSummation LacunaryVerySmallRange
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CanonicalScaleAtoms
open PositiveLowFullEstimate
open PositiveHighHeightEstimate
open PositiveEndpointOptimization
set_option autoImplicit false
end LacunaryVerySmallOperator
end QuadraticCarleson

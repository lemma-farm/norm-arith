/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleOperator
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KaltonPaperApplication
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryVerySmallEndpoint
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Kalton applied to the genuine frozen modulation-block outputs

The functions in this file are the concrete low-kernel actions from
`LacunaryMiddleOperator`, not an abstract family. The only conditional
analytic input is an individual frozen-block weak-L¹ estimate. Countable
suprema, level summation, measurability, and the fivefold exceptional-set
contribution are all discharged here.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace LacunaryMiddleKalton
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveEndpointOptimization PositiveLowFullEstimate
open LacunaryMiddleOperator KaltonPaperApplication LacunaryVerySmallEndpoint
set_option autoImplicit false
end LacunaryMiddleKalton
end QuadraticCarleson

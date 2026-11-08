/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LowKernelRealMaximal
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositiveHighHeightFullEndpoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The low kernel applied to the genuine countable atom sum

For each fixed modulation the telescoped low kernel is globally bounded.
The levelwise atom masses are summable for integrable input, so the Bochner
integral commutes with their countable sum. No formal integral interchange
is left as an assumption.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveLowFullEstimate
open CalderonZygmundLevelAtoms LowKernelLevelSummation
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate
end PositiveLowFullEstimate
end QuadraticCarleson

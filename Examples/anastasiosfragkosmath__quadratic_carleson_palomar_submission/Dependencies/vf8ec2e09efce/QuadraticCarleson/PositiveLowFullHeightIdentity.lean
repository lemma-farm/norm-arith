/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositiveLowFullEndpoint
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Exact agreement with the paper's finite low-height sum

This file commutes the finite height sum with the integral and changes
variables to the paper's `b(x-t) ψ_j(t) e(λt²)` convention. Consequently the
endpoint bound applies literally to the all-level finite-height formula.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveLowFullEstimate
open CalderonZygmundLevelAtoms PositiveEndpointOptimization PositiveHighHeightEstimate
end PositiveLowFullEstimate
end QuadraticCarleson

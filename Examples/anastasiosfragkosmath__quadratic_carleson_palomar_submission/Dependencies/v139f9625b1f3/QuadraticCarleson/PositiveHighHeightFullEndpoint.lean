/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveHighHeightWeighted
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveHighHeightConvergence
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The full-operator high contribution is bounded by the L log L modular

We make the paper's unspecified large cutoff constant explicit: `B_k = 20·2^k`.
With the proved exponent `β = 1/10`, the numerical high-frequency series is
summable. This theorem needs an explicit disjoint interval family, but no
construction of a Calderón--Zygmund decomposition and no unproved operator
estimate.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveHighHeightEstimate
open CalderonZygmundLevelAtoms PositiveLevelIntegration PositiveEndpointOptimization
end PositiveHighHeightEstimate
end QuadraticCarleson

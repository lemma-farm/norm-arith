/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositiveHighHeightFullEndpoint
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The lacunary high contribution

The lacunary amplitude levels use the exact integer cutoff `20·2^(2^k)`.
The already proved real-parameter quadratic decay is stronger than needed for
the lacunary modulation set. We first estimate that real-parameter high part,
and then restrict the supremum to the paper's dyadic modulations.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveHighHeightEstimate
open CalderonZygmundLevelAtoms PositiveLevelIntegration PositiveEndpointOptimization
end PositiveHighHeightEstimate
end QuadraticCarleson

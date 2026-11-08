/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositiveHighHeightSummation
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Weighted Cauchy--Schwarz for the actual high contribution

The free positive weight can be chosen as `B_k` for the full operator, or as
`log₁(B_k)²` for the lacunary optimization. This is the last analytic bound
in the paper's high-height argument, with the fixed exponent `β = 1/10`.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveHighHeightEstimate
open CalderonZygmundLevelAtoms PositiveLevelIntegration
end PositiveHighHeightEstimate
end QuadraticCarleson

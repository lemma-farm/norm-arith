/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleKalton
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositiveHighHeightLacunaryEndpoint
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Finite residue summation and the final lacunary middle Orlicz budget

The sparse modulus remains the paper's exact `10^10`. Summing a complete
finite residue system contributes only that universal factor. The independent
factor `20` occurs in the height cutoff `B_k = 20 · 2^(2^k)`.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace LacunaryMiddleFinalSummation
open LacunaryMiddleRange LacunaryMiddleOperator LacunaryMiddleKalton
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate
open CalderonZygmundStoppingIntervals PositiveLowFullEstimate
set_option autoImplicit false
end LacunaryMiddleFinalSummation
end QuadraticCarleson

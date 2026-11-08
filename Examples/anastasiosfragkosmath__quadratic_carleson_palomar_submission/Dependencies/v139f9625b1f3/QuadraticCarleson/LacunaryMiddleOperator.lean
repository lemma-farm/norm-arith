/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.LacunaryVerySmallOperator
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.CanonicalScaleAtomIntegrals
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.FiniteModulationKernelComparison
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.QuadraticHilbertMaximalMeasurable
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Genuine inputs for the lacunary middle-range argument

This module realizes the three functions occurring in source lines 636--648:
the actual middle-scale input, its frozen `R_{k,τ}` replacement, and the
signed error.  It proves their exact algebraic recombination and the
disjoint-scale `L¹` packing needed before the finite-modulation estimate and
Kalton log-convexity are applied.
-/
open Function MeasureTheory Set
open scoped ENNReal BigOperators
namespace QuadraticCarleson
namespace LacunaryMiddleOperator
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms
open CanonicalScaleAtoms LacunaryMiddleRange LacunaryMiddleRangeSummation
open LacunaryLowSupport LacunaryVerySmallOperator PositiveEndpointOptimization
open LowKernelLevelSummation PositiveLowFullEstimate
open QuadraticHilbertMaximalMeasurable
set_option autoImplicit false
noncomputable section
end
end LacunaryMiddleOperator
end QuadraticCarleson

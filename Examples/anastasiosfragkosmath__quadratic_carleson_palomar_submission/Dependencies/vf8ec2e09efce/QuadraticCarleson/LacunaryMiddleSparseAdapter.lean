/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceyFiniteRadiusAdapter
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryFrozenInputL0
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleFiniteRadiusLimit
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Applying a finite sparse maximum to the genuine frozen block

This module contains the exact adapter between the abstract finite sparse
maximal theorem and the frozen quadratic-Hilbert block in the paper.  It
indexes the modulation block `Q B τ` by a finite type, applies the resulting
finite maximum to the genuine compactly supported frozen input, and passes a
uniform finite-radius weak bound to the full real-radius supremum.
-/
open MeasureTheory Set
open scoped ENNReal NNReal
namespace QuadraticCarleson
namespace LacunaryMiddleSparseAdapter
open ExtendedWeakL1Combinators KaltonPaperApplication
open KrauseLaceyFiniteRadiusAdapter LacunaryFrozenInputL0
open LacunaryMiddleFiniteRadiusLimit LacunaryMiddleOperator LacunaryMiddleRange
open QuadraticHilbertMaximalMeasurable
open PositiveEndpointOptimization CalderonZygmundDyadicStopping
open CalderonZygmundStoppingIntervals
open PositiveLowFullEstimate
set_option autoImplicit false
noncomputable section
end
end LacunaryMiddleSparseAdapter
end QuadraticCarleson

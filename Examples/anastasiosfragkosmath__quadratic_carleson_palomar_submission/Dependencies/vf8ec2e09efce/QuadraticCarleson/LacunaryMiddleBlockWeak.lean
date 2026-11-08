/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.ExtendedWeakL1Combinators
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleKalton
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Reduction of a frozen middle block to a finite quadratic-Hilbert block

This file applies the smooth-kernel comparison to the genuine frozen inputs.
It isolates the remaining finite-modulation estimate at precisely the sharp
quadratic Hilbert maximal truncation occurring in the paper.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace LacunaryMiddleBlockWeak
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveEndpointOptimization PositiveLowFullEstimate
open KaltonPaperApplication ExtendedWeakL1Combinators
open LacunaryMiddleOperator LacunaryMiddleKalton
set_option autoImplicit false
end LacunaryMiddleBlockWeak
end QuadraticCarleson

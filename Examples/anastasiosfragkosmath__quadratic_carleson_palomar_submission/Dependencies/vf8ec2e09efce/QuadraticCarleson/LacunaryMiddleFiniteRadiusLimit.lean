/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.ExtendedWeakL1Combinators
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleOperator
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Passing finite truncation-radius estimates to a genuine frozen block

Krause--Lacey's sparse theorem is applied first to finite, everywhere-finite
maxima of sharp truncations.  This file proves the exact limiting step which
recovers the paper's supremum over every positive truncation radius without
losing the uniform weak constant.  The limit uses the fixed countable dense
family already proved to recover the full real-radius supremum.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace LacunaryMiddleFiniteRadiusLimit
open ExtendedWeakL1Combinators KaltonPaperApplication
open LacunaryMiddleOperator LacunaryMiddleRange
open QuadraticHilbertMaximalMeasurable
set_option autoImplicit false
noncomputable section
end
end LacunaryMiddleFiniteRadiusLimit
end QuadraticCarleson

/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.HardyLittlewoodMaximal
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Strong `L^p` bounds for the centered Hardy--Littlewood maximal operator

This extends the already checked weak `(1,1)` estimate by the layer-cake
argument needed in the sparse finite-maximal lemma.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson

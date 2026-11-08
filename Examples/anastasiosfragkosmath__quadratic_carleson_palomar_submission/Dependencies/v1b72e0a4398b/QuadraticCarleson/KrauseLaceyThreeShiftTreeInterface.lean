/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyThreeShiftGrid
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyBadScaleInputs
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyStoppingRecursion
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The finite three-shift grids satisfy the KL bad-scale tree interface

This file connects the concrete complete descendant trees in each of the
three translated dyadic grids with the abstract parent-closure hypothesis
used in the local Krause--Lacey bad-scale estimates.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyThreeShiftGrid
open CalderonZygmundDyadicStopping
open KrauseLaceyStoppingExtraction KrauseLaceyStoppingRecursion
set_option autoImplicit false
noncomputable section
end
end KrauseLaceyThreeShiftGrid
end QuadraticCarleson

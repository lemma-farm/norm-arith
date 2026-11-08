/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.CalderonZygmundBadPart
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The logarithmic low-oscillatory majorant

The low part of the positive theorem is bounded off a Calderón--Zygmund atom
by

`min (1 / d) (D * ℓ / d²)`.

This file proves the exact one-dimensional integral behind the paper's
`O(B)` estimate.  The transition occurs at distance `D * ℓ`: the first part
integrates to `log D`, and the inverse-square tail integrates to `1`.
-/
open MeasureTheory Set
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson

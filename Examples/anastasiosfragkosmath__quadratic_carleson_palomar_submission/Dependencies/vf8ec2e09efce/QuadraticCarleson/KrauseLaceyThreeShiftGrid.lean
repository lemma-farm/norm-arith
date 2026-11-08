/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CalderonZygmundDyadicStopping
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceyShiftedLocalization
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The finite three-shift grids in the Krause--Lacey reduction

For a largest scale, each of the three grids is an ordinary global dyadic
grid translated by zero, one third, or two thirds of the largest length.
At every finer scale the three translations are permuted modulo one, so the
central thirds partition the line.  This file first establishes the exact
laminar geometry within each translated grid.  The finite support and
three-grid reconstruction are developed from this representation below.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyThreeShiftGrid
open CalderonZygmundDyadicStopping
set_option autoImplicit false
noncomputable section
end
end KrauseLaceyThreeShiftGrid
end QuadraticCarleson

/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleMainTerm
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleOperatorAction
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The oscillatory packet sum in the negative endpoint example

This file bounds the contribution of the packets to the left of an admissible
observation point.  The exact lower edge of the paper's exponent window turns
the two-fold oscillatory estimate into a geometric series.
-/
open Finset Set
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson

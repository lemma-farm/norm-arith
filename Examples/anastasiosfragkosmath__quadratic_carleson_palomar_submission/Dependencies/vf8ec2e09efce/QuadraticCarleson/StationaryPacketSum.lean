/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleMainTerm
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleOperatorAction
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleStationaryMain
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Stationary packet sum

The packets to the right of a translate are off support at `k + τ`, and their
kernel actions can be replaced by their finite phase main terms.  This file
keeps the dyadic window and its resulting geometric decay explicit.
-/
open Finset Set
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson

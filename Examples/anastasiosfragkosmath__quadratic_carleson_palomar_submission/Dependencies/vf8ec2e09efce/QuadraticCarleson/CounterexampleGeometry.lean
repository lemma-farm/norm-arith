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
# Spatial geometry of the negative-endpoint packets

An admissible point has the form `x = k + τ`, where `k` is one of the paper's
translate indices and `τ ∈ (1/4,1/2)`.  This file records the elementary
separation from all packet intervals, together with lower bounds that retain
the integer separation from the packet centre.
-/
open Finset MeasureTheory Set
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson

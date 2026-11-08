/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleParameters
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexamplePointwise
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The asymptotic error budget in the negative endpoint example

For the explicit choice `A_N = 2⁻⁴⁰ log N`, the stationary error is a
small fixed fraction of the harmonic main term, the packet-scale error decays
geometrically, and the two-fold oscillatory error is `O((log N)⁻²)`.  This
module proves that their sum eventually fits below the unused half of the
main-term lower bound.
-/
open Filter
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson

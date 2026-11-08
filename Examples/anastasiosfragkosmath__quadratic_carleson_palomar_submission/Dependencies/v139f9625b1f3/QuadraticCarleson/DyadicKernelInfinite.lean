/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveDyadicKernel
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Infinite telescoping of the positive-proof dyadic kernel

For a fixed nonzero spatial point, only finitely many of the dyadic pieces
`ψ_{j+r}` with `r ≥ 0` are nonzero.  Their infinite sum therefore telescopes
exactly to the high-pass kernel used in the paper's oscillatory reduction.
-/
open Filter Function Set
open scoped Topology BigOperators
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson

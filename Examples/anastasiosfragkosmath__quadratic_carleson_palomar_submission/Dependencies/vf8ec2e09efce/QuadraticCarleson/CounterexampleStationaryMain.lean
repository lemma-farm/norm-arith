/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleMainTerm
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Identification of the stationary kernel main term

The packet estimate produces phases `e(λ(x-j)²)`, whereas the Bohr argument
uses `e(2λjx)`.  For dyadic (hence integer) `λ`, the `λj²` phase is one and
the sign change is complex conjugation.  This file records the exact identity,
so the two finite sums have precisely the same norm.
-/
open Set
open scoped ComplexConjugate
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson

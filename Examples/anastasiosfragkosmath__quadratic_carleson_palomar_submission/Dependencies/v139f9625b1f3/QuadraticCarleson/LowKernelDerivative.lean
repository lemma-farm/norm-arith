/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveDyadicKernel
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Derivative of the low oscillatory kernel

In the accompanying article ([arXiv:2609.04101v1](https://arxiv.org/abs/2609.04101v1)), the low kernel
`K_{λ,B}` is asserted to satisfy
`|K'_{λ,B}(t)| ≲ min {|λ|, 2^(2B)/|t|²}`.  This file records the exact
product/quotient-rule formula away from zero and derives its constants from
the fixed smooth cutoff used by `PositiveDyadicKernel`.
-/
open Function Set
open scoped Topology
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson

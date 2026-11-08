/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.LowKernelDerivative
import Mathlib.Analysis.Calculus.MeanValue
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Calderón--Zygmund regularity of the low oscillatory kernel

This file turns the derivative estimate for the paper's low kernel into the
kernel-difference estimate used on a mean-zero Calderón--Zygmund atom.  The
mean-value theorem is applied on the segment joining `x - y` and `x - z`.
When `y` belongs to the interval centered at `z` and `x` is outside its
triple, every point of that segment stays quantitatively away from zero.
-/
open MeasureTheory Set
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson

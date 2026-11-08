/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.QuadraticCenteredMaximal
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.QuadraticL2Operator
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Symmetric averaging bounds for the quadratic `TT*` argument

The correlation estimate is majorized by centered averages at a radius selected
by either endpoint. The bound here is independent of the number of radii and
their size. It is the positive-kernel part of the operator-level argument.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open scoped ComplexConjugate
namespace QuadraticCarleson
namespace FiniteRangeKernel
end FiniteRangeKernel
end QuadraticCarleson

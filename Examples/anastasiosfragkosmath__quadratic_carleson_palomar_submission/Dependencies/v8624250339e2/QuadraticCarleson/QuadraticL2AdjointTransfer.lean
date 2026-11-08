/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.QuadraticL2Extension
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Transferring the adjoint bound to the integral operator

The elementary `TT*` duality argument is carried out on the actual integral
actions, then extended to all measurable `L²` inputs by spatial truncation.
-/
open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate
namespace QuadraticCarleson
namespace FiniteRangeKernel
end FiniteRangeKernel
end QuadraticCarleson

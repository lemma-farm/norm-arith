/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.QuadraticAveragingTTStar
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Extending finite-range integral estimates beyond test inputs

Spatial truncations eventually leave each kernel row unchanged. Fatou's lemma
therefore extends uniform second-moment bounds from integrable test functions
to locally integrable functions, in particular to all measurable `L²` inputs.
-/
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace QuadraticCarleson.FiniteRangeKernel
end QuadraticCarleson.FiniteRangeKernel

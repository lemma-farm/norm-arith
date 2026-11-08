/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.OscillatoryReductionSeries
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.L0LacunaryOperator
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Reduction of quadratic principal-value truncations to oscillatory heights

The right side consists of the genuine nonnegative-height oscillatory series,
the ordinary (zero-modulation) Hilbert maximal truncation, and the measurable
centered Hardy--Littlewood maximal function. No principal-value existence or
Hilbert-transform boundedness assertion is used as a hypothesis.
-/
open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology
namespace QuadraticCarleson
namespace OscillatoryReduction
end OscillatoryReduction
end QuadraticCarleson

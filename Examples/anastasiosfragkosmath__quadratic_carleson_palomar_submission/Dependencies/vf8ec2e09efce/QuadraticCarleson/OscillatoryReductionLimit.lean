/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.OscillatoryReductionMaximal
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The regular difference between quadratic and ordinary Hilbert truncations

For every bounded compactly supported measurable input, every observation
point, and every nonzero modulation, subtracting the ordinary Hilbert
truncation leaves a convergent quantity. The only classical principal-value
existence issue is therefore that of the ordinary Hilbert transform.
-/
open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace QuadraticCarleson
namespace OscillatoryReduction
end OscillatoryReduction
end QuadraticCarleson

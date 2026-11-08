/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.OscillatoryReductionKernel
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositiveLowFullHeightIdentity
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The exact oscillatory series on the paper's test domain

For fixed observation point and modulation, compact support of the input
makes every sufficiently high dyadic term identically zero. Thus all
integral/series interchanges below are genuine and require no convergence
hypothesis beyond membership in `L0Infinity`.
-/
open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace QuadraticCarleson
namespace OscillatoryReduction
end OscillatoryReduction
end QuadraticCarleson

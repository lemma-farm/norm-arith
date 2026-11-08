/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.DyadicKernelInfinite
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.FiniteModulationKernelComparison
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.HarmonicPhaseSum
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Exact scalar kernels for the oscillatory reduction

The inner radius is dictated by the selected scale, not chosen independently.
The high-pass kernel is exactly the sum of all nonnegative oscillatory heights.
Subtracting two ordinary Hilbert truncations leaves a boundary annulus and a
small-phase error supported in the inner interval.
-/
open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace QuadraticCarleson
namespace OscillatoryReduction
end OscillatoryReduction
end QuadraticCarleson

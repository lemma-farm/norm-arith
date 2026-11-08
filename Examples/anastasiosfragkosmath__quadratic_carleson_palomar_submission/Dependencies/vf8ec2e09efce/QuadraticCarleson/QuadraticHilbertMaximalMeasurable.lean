/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.FiniteModulationKernelComparison
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.HilbertFiniteTruncationWeakOneOne
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IsLUB
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Measurability of the quadratic maximal truncation

For every real quadratic modulation, the sharp truncation is continuous in
its positive radius.  Hence its supremum over all positive real radii equals
a supremum over one fixed countable dense family and is measurable.  The
argument applies to every measurable integrable input.
-/
open Filter Function MeasureTheory Set
open scoped ENNReal Topology
namespace QuadraticCarleson
namespace QuadraticHilbertMaximalMeasurable
open HilbertFiniteTruncationWeakOneOne
set_option autoImplicit false
noncomputable section
end
end QuadraticHilbertMaximalMeasurable
end QuadraticCarleson

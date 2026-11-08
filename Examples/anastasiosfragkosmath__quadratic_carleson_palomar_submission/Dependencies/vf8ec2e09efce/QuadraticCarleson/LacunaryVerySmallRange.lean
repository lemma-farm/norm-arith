/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleRange
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Geometric summation in the lacunary very-small range

For `j ∈ L B c m`, the paper's very-small contribution has weight
`2^(B + m/2 + j)`.  Here the exponent is interpreted in `ℝ`, exactly as in
the displayed analytic estimate.  For fixed `j`, the allowed modulation
indices form a left half-line.  Reindexing that half-line by `ℕ` gives a
geometric series of ratio `2^(-1/2)`.

The final theorem is stated in `ℝ≥0∞`, so the exchange of the two countable
sums is genuine Tonelli and requires no summability assumption on the
nonnegative coefficients.
-/
open Set
namespace QuadraticCarleson.LacunaryVerySmallRange
set_option autoImplicit false
open QuadraticCarleson.LacunaryMiddleRange
end QuadraticCarleson.LacunaryVerySmallRange

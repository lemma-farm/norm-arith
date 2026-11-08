/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.Bohr
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The dyadic kernels used in the positive estimate

This file records the elementary, exact part of the dyadic decomposition of
the quadratic Hilbert kernel.  The quotient defining a dyadic piece is given
the value zero at the origin; this is not an arbitrary extension, since the
numerator vanishes on a whole neighbourhood of the origin.
-/
open Function Set
open scoped ContDiff Topology
namespace QuadraticCarleson
/- The bump supplied by `ContDiffBump` is one on the inner closed ball and is
supported in the outer open ball.  With these radii those balls are exactly
the two intervals required in the paper. -/
noncomputable def dyadicCutoffData : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
noncomputable def dyadicCutoff : ℝ → ℝ := dyadicCutoffData
theorem dyadicCutoff_smooth : ContDiff ℝ ∞ dyadicCutoff := by
  exact dyadicCutoffData.contDiff
theorem dyadicCutoff_nonneg (x : ℝ) : 0 ≤ dyadicCutoff x := by
  exact dyadicCutoffData.nonneg
theorem dyadicCutoff_le_one (x : ℝ) : dyadicCutoff x ≤ 1 := by
  exact dyadicCutoffData.le_one
theorem dyadicCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1 / 4) :
    dyadicCutoff x = 1 := by
  apply dyadicCutoffData.one_of_mem_closedBall
  simpa [dyadicCutoffData, Metric.mem_closedBall, Real.dist_eq] using hx
theorem dyadicCutoff_eq_zero {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    dyadicCutoff x = 0 := by
  apply dyadicCutoffData.zero_of_le_dist
  simpa [dyadicCutoffData, Real.dist_eq] using hx
end QuadraticCarleson

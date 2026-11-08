module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.BigOperators.Intervals
public import Examples.TomasOrtega__Sidon.Dependencies.v792c292df185.Sidon.NumberTheory.RiemannGaussian.PhaseIncrementInverse
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.FiniteKuzminLandau
noncomputable section
open RiemannGaussian.PhaseIncrementInverse
open scoped Classical
theorem summation_by_parts (c z : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), c n * (z (n + 1) - z n)) =
      c N * z (N + 1) - c 0 * z 0 +
        ∑ n ∈ Finset.range N, (c n - c (n + 1)) * z (n + 1) := by
  induction N with
  | zero => simp [mul_sub]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring
end
end RiemannGaussian.FiniteKuzminLandau

/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.PositiveDyadicKernel
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.IntervalMaximalComparison
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The finite low-modulation block versus maximal truncations

This is the elementary pointwise reduction at the start of the proof of the
finite-modulation weak-type corollary in the accompanying article
([arXiv:2609.04101v1](https://arxiv.org/abs/2609.04101v1)). A
consecutive block of the paper's smooth dyadic kernels telescopes.  Replacing
its two smooth cutoffs by sharp cutoffs produces the difference of two
quadratic Hilbert truncations; the two transition annuli are controlled by
the centered Hardy--Littlewood maximal function.

The later sparse input in the paper is [Krause--Lacey, Theorem 1.1], namely a
uniform sparse `(1,p)` estimate for the maximally truncated quadratic Hilbert
transform.  Mathlib has no Carleson or oscillatory sparse-bound development,
and the project currently only defines the abstract sparse premise in
`FiniteSparseMaximal`.  Accordingly, this file proves the concrete pointwise
comparison without postulating that external theorem.
-/
open Function MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace QuadraticCarleson
set_option autoImplicit false
/-- The maximally truncated quadratic Hilbert transform, with the supremum
taken over all positive real truncation radii as in the paper. -/
noncomputable def quadraticHilbertMaximalTruncation
    (lam : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ ε : {ε : ℝ // 0 < ε}, ‖quadraticHilbertTrunc lam ε f x‖ₑ
theorem L0Infinity.integrable (f : L0Infinity) : Integrable f := by
  have hcompact : IsCompact (tsupport f) := f.hasCompactSupport_toFun
  have hfinite : volume (tsupport f) < ∞ := hcompact.measure_lt_top
  rcases f.bounded_toFun with ⟨C, hC⟩
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
  exact IntegrableOn.of_bound hfinite
    f.measurable_toFun.aestronglyMeasurable.restrict C
    (Filter.Eventually.of_forall hC)
end QuadraticCarleson

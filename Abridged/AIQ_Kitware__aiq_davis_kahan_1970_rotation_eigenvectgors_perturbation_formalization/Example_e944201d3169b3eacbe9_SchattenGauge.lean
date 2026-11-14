module

public import Mathlib.Analysis.MeanInequalities

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Examples.Example_e944201d3169b3eacbe9_SchattenGauge ====
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# The `ℓᵖ` symmetric gauge

`Φ_p a = (∑ aₙ ^ p) ^ (1 / p)` for `1 ≤ p`, as a `TauCeti.SymmetricGauge` on
finitely supported nonnegative sequences.  Feeding it to
`TauCeti.symmetricGaugeFamily` produces the Schatten-`p` operator ideal family.

* `TauCeti.schattenGaugeFun` — the underlying function;
* `TauCeti.schattenGauge` — the bundled gauge.

## Sums over a larger index set

The gauge is a sum over `a.support`, but its subadditivity compares three
sequences with three different supports.  `schattenGaugeFun_eq_sum_of_subset`
says the sum may be taken over any `Finset` containing the support — the extra
terms are `0 ^ p = 0`, which needs `p ≠ 0` — so all three can be moved to the
union of their supports before Minkowski applies.  That bookkeeping, rather than
the inequality, is the substance of `add_le`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new**.  Written against the target signature in
  `TauCetiRoadmap/OperatorTheory/OperatorIdeals/Suggested.lean`.
* Roadmap topic: `OperatorIdeals`.
* Original authors / copyright: Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
-/
public section
open scoped NNReal ENNReal
namespace TauCeti
variable {p : ℝ}
/-- The underlying `ℓᵖ` gauge function on finitely supported nonnegative
sequences. -/
@[expose]
noncomputable def schattenGaugeFun (p : ℝ) (a : ℕ →₀ ℝ≥0) : ℝ≥0 :=
  (∑ i ∈ a.support, a i ^ p) ^ (1 / p)

set_option linter.unusedVariables false in
/-- **The `ℓ` scale nests.**  For `1 ≤ p ≤ q` the `ℓ^q` gauge is below the `ℓ^p`
gauge.

Normalization: each `cₙ` is below `M = Φ_p c`, so `cₙ/M ≤ 1` and raising to the
larger exponent `q` only decreases it; summing gives `∑ cₙ^q ≤ M^q`.  The case
`M = 0` is separate, since there is nothing to divide by — there `c = 0`. -/
theorem schattenGaugeFun_antitone (hp : 1 ≤ p) {q : ℝ} (hq : 1 ≤ q) (hpq : p ≤ q)
    (c : ℕ →₀ ℝ≥0) 
    (h_TauCeti_le_schattenGaugeFun : ∀ {p : ℝ}, 1 ≤ p → ∀ (c : ℕ →₀ NNReal) (i : ℕ), (c : ℕ → NNReal) i ≤ TauCeti.schattenGaugeFun p c)
    : schattenGaugeFun q c ≤ schattenGaugeFun p c := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set M := schattenGaugeFun p c with hM
  -- No case split on `M = 0` is needed: `rpow_add_of_nonneg` holds there too,
  -- and when `M = 0` every coordinate is `0`, so the termwise bound is `0 ≤ 0`.
  have hMp : M ^ p = ∑ i ∈ c.support, c i ^ p := by
    rw [hM, schattenGaugeFun, ← NNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hp0.ne', NNReal.rpow_one]
  have hterm : ∀ i ∈ c.support, c i ^ q ≤ c i ^ p * M ^ (q - p) := by
    intro i _
    have hle : c i ≤ M := h_TauCeti_le_schattenGaugeFun hp c i
    calc c i ^ q = c i ^ (p + (q - p)) := by congr 1; ring
      _ = c i ^ p * c i ^ (q - p) :=
          NNReal.rpow_add_of_nonneg _ (by linarith) (by linarith)
      _ ≤ c i ^ p * M ^ (q - p) := by
          gcongr
  have hsum : ∑ i ∈ c.support, c i ^ q ≤ M ^ q := by
    calc ∑ i ∈ c.support, c i ^ q
        ≤ ∑ i ∈ c.support, c i ^ p * M ^ (q - p) := Finset.sum_le_sum hterm
      _ = (∑ i ∈ c.support, c i ^ p) * M ^ (q - p) := by rw [← Finset.sum_mul]
      _ = M ^ p * M ^ (q - p) := by rw [hMp]
      _ = M ^ q := by
          rw [← NNReal.rpow_add_of_nonneg _ (by linarith : (0:ℝ) ≤ p)
            (by linarith : (0:ℝ) ≤ q - p)]
          congr 1
          ring
  calc schattenGaugeFun q c = (∑ i ∈ c.support, c i ^ q) ^ (1 / q) := rfl
    _ ≤ (M ^ q) ^ (1 / q) := NNReal.rpow_le_rpow hsum (by positivity)
    _ = M := by rw [← NNReal.rpow_mul, mul_one_div, div_self hq0.ne', NNReal.rpow_one]
end TauCeti

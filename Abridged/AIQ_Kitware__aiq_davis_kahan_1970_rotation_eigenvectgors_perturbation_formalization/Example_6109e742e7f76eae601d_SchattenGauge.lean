module

public import Mathlib.Analysis.MeanInequalities

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Examples.Example_6109e742e7f76eae601d_SchattenGauge ====
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
theorem schattenGaugeFun_add_le (hp : 1 ≤ p) (a b : ℕ →₀ ℝ≥0) 
    (h_TauCeti_schattenGaugeFun_eq_sum_of_subset : ∀ {p : ℝ},
      0 < p →
        ∀ (a : ℕ →₀ NNReal) {s : Finset ℕ},
          a.support ⊆ s → TauCeti.schattenGaugeFun p a = (∑ i ∈ s, (a : ℕ → NNReal) i ^ p) ^ (1 / p))
    :
    schattenGaugeFun p (a + b) ≤ schattenGaugeFun p a + schattenGaugeFun p b := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set s : Finset ℕ := a.support ∪ b.support with hs
  have hab : (a + b).support ⊆ s := by
    intro i hi
    simpa [hs] using Finsupp.support_add hi
  have eab : schattenGaugeFun p (a + b) = (∑ i ∈ s, (a i + b i) ^ p) ^ (1 / p) := by
    rw [h_TauCeti_schattenGaugeFun_eq_sum_of_subset hp0 _ hab]
    rfl
  have ea : schattenGaugeFun p a = (∑ i ∈ s, a i ^ p) ^ (1 / p) :=
    h_TauCeti_schattenGaugeFun_eq_sum_of_subset hp0 a Finset.subset_union_left
  have eb : schattenGaugeFun p b = (∑ i ∈ s, b i ^ p) ^ (1 / p) :=
    h_TauCeti_schattenGaugeFun_eq_sum_of_subset hp0 b Finset.subset_union_right
  rw [eab, ea, eb]
  exact NNReal.Lp_add_le s (fun i => a i) (fun i => b i) hp
end TauCeti

/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Examples.mario_ullrich__Lean_SNumbers.Dependencies.vfe65697966c2.SNumbers.Helpers
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# Approximation numbers

The approximation numbers are the *largest* example of an s-number sequence.
They are defined as

`a_n S = inf { ‖S - L‖ : L : X →L[𝕜] Y, rank L ≤ n }`.

In this file we prove that the approximation numbers satisfy all five
Pietsch axioms (S1)–(S5). In fact we prove the stronger normalisation
(S5') — `a_n (id_X) = 1` for every Banach space `X` with `dim X > n` —
via Riesz's lemma; (S5) on `ℓ₂^{n+1}` is the corresponding specialisation.
The argument requires `[CompleteSpace 𝕜]` (so that finite-dimensional
subspaces are closed) but is otherwise elementary.

We also prove here that the approximation numbers are the **largest**
s-number sequence (`sn_le_approximationNumber` : `sₙ(S) ≤ aₙ(S)` for every
s-number sequence `s`).

## Main definitions

* `SNumbers.approximationNumber S n` — the `n`-th approximation number of `S`.

## Main results

* `SNumbers.approximationNumber_zero_eq_norm` : `a_0 S = ‖S‖`              (S1a)
* `SNumbers.approximationNumber_antitone` : `a_{n+1} S ≤ a_n S`            (S1b)
* `SNumbers.approximationNumber_nonneg` : `0 ≤ a_n S`                      (S1c)
* `SNumbers.approximationNumber_add_le` : `a_n (S + T) ≤ a_n S + ‖T‖`      (S2)
* `SNumbers.approximationNumber_comp_comp_le` :
    `a_n (B ∘ S ∘ A) ≤ ‖B‖ * a_n S * ‖A‖`                                   (S3)
* `SNumbers.approximationNumber_eq_zero_of_rank_le` :
    `rank S ≤ n ⇒ a_n S = 0`                                                (S4)
* `SNumbers.approximationNumber_strict` :
    `dim X > n ⇒ a_n (id_X) = 1`                                            (S5')
* `SNumbers.approximationNumber_id_euclidean` :
    `a_n (id_{ℓ₂^{n+1}}) = 1`                                               (S5)
* `SNumbers.isStrictSNumberSequence_approximationNumber` :
    the approximation numbers form a *strict* s-number sequence.
* `SNumbers.sn_le_approximationNumber` : `s_n S ≤ a_n S` for every s-number
    sequence `s` — the approximation numbers are the largest.
-/
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
/-- The set of approximation residuals `‖S - L‖` over operators `L` of rank
at most `n`. -/
def approximationSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ L : X →L[𝕜] Y, L.rank ≤ (n : Cardinal) ∧ r = ‖S - L‖}
/-- The `n`-th **approximation number** of a continuous linear map: the
infimum of `‖S - L‖` over operators `L` of rank at most `n`. -/
noncomputable def approximationNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (approximationSet S n)
/-! ### Basic properties of `approximationSet` -/
lemma bddBelow_approximationSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (approximationSet S n) :=
  ⟨0, by rintro r ⟨L, _, rfl⟩; exact norm_nonneg _⟩
/-- Convenience: every operator `L` of rank ≤ n provides an upper bound for
the approximation number. -/
lemma approximationNumber_le_norm_sub {S : X →L[𝕜] Y} {n : ℕ}
    {L : X →L[𝕜] Y} (hL : L.rank ≤ (n : Cardinal)) :
    approximationNumber S n ≤ ‖S - L‖ :=
  csInf_le (bddBelow_approximationSet S n) ⟨L, hL, rfl⟩
/-! ### (S1c) Non-negativity -/
variable [CompleteSpace 𝕜]
end SNumbers

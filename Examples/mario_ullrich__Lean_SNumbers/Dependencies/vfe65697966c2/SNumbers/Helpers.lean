/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Examples.mario_ullrich__Lean_SNumbers.Dependencies.vfe65697966c2.SNumbers.Basic
import Mathlib.Analysis.Normed.Group.Quotient
/-!
# Helpers shared across s-number constructions

A small library of utilities used by more than one s-number construction.
None of the content here is specific to a particular `s`-number sequence.

* Rank facts about continuous linear maps:
  `ContinuousLinearMap.rank_zero`, `eq_zero_of_rank_le_zero`,
  `rank_comp_comp_le`. The bare definition `ContinuousLinearMap.rank` lives
  in `SNumbers.Basic`.
* `ContinuousLinearMap.opNorm_le_of_unit_closedBall` — a bound on the closed
  unit ball bounds the operator norm (densely normed scalars).
* `Submodule.norm_mkQL_le` and `Submodule.norm_mkQL_apply_le` — operator-norm
  bound `‖V.mkQL‖ ≤ 1` for the quotient projection `Submodule.mkQL`, and its
  pointwise form `‖V.mkQL y‖ ≤ ‖y‖`.
* `Submodule.norm_liftQL_le` — operator-norm bound `‖V.liftQL f h‖ ≤ ‖f‖`
  for the universal lift `Submodule.liftQL`, plus the computation rule
  `Submodule.liftQL_mkQL`.
* `SNumbers.finrank_euclideanSpace_fin'` — `finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n`
  over any `NontriviallyNormedField` (Mathlib's `finrank_euclideanSpace_fin`
  needs `RCLike`), used by the `(S5)` normalisations of every s-number.

Mathlib ships the `ContinuousLinearMap` wrappers `Submodule.mkQL` and
`Submodule.liftQL` (in
`Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient`) for general
topological modules but without operator-norm information; the lemmas here
add the missing norm bounds in the normed setting.
-/
universe u
open scoped Cardinal
namespace ContinuousLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
section Rank
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end Rank
section CompRank
-- Comparing the ranks of operators with different domain/codomain forces a
-- single universe for `Cardinal` to be well-defined.
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
/-- The rank of a composition is bounded by the rank of the middle factor. -/
lemma rank_comp_comp_le (A : W →L[𝕜] X) (L : X →L[𝕜] Y) (B : Y →L[𝕜] Z) :
    (B.comp (L.comp A)).rank ≤ L.rank := by
  have hsub :
      LinearMap.range (B.comp (L.comp A) : W →ₗ[𝕜] Z) ≤
        Submodule.map (B : Y →ₗ[𝕜] Z) (LinearMap.range (L : X →ₗ[𝕜] Y)) := by
    intro z hz
    obtain ⟨w, hw⟩ := hz
    exact ⟨L (A w), ⟨A w, rfl⟩, by simpa using hw⟩
  calc Module.rank 𝕜 (LinearMap.range (B.comp (L.comp A) : W →ₗ[𝕜] Z))
      ≤ Module.rank 𝕜
          (Submodule.map (B : Y →ₗ[𝕜] Z) (LinearMap.range (L : X →ₗ[𝕜] Y))) :=
        Submodule.rank_mono hsub
    _ ≤ Module.rank 𝕜 (LinearMap.range (L : X →ₗ[𝕜] Y)) :=
        rank_map_le _ _
end CompRank
section UnitBall
/-! The operator norm is the supremum of `‖f x‖` over the *closed unit ball*
only when the scalar norms are dense: over a discretely valued field one can
never rescale a vector to have norm exactly `1`, and the supremum over the
unit ball may fall short of `‖f‖`. Mathlib's
`ContinuousLinearMap.sSup_unitClosedBall_eq_norm` is stated in exactly that
`DenselyNormedField` setting; the lemma below is the bound-form we need. The
codomain may be merely seminormed, which matters because our applications take
values in a quotient `Y ⧸ V`. -/
variable {𝕜' : Type*} [DenselyNormedField 𝕜']
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜' E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜' F]
end UnitBall
end ContinuousLinearMap
/-! ## Operator-norm bounds for the quotient CLMs `Submodule.mkQL` / `liftQL`

Mathlib (`Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient`)
provides `Submodule.mkQL` — the quotient projection `Y →L[𝕜] (Y ⧸ V)` — and
`Submodule.liftQL` — the universal lift of a continuous linear map through
that quotient — for general *topological* modules, but without any
operator-norm information. In the normed setting the projection is a
contraction (`‖V.mkQL‖ ≤ 1`) and the lift does not increase the norm
(`‖V.liftQL f h‖ ≤ ‖f‖`). We record those two bounds here, together with the
computation rule `V.liftQL f h (V.mkQL y) = f y`. -/
namespace Submodule
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {Y Z : Type*}
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
end Submodule
namespace SNumbers
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
end SNumbers

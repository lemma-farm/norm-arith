module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_1108644498c585b34eda_FixedPointBanach ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The abstract fixed-point argument for `u = 𝒦 (F u) + v`

This is the functional-analytic core of [Hai14, Theorem 7.8], with every hypothesis explicit.
`X` (the space of solutions, `D^{γ,η}_P` on a time slab) is a complete normed group, `Y` (the
space of right-hand sides, `D^{γ̄,η̄}_P` on the slab) a normed group,

* `𝒦 : Y → X` is additive with `‖𝒦 y‖ ≤ c ‖y‖` (on a slab of length `T`, `c = C T^θ`: the
  short-time gain of [Hai14, Theorem 7.1, Lemma 7.3]);
* `F : X → Y` is Lipschitz on balls, `‖F u − F u'‖ ≤ L(R) ‖u − u'‖` for `‖u‖, ‖u'‖ ≤ R`, with
  `L(R) = L₀ (1 + R)^p` polynomial in the radius, and `‖F 0‖ ≤ A`;
* `v ∈ X` is the datum, `‖v‖ ≤ V`.

Main statements:

* `exists_unique_fixedPoint_of_ball`: if `‖v‖ + c (A + L R) ≤ R` and `c L < 1`, the map
  `u ↦ 𝒦 (F u) + v` has a unique fixed point in the closed ball of radius `R` (Banach's fixed
  point theorem, `ContractingWith.exists_fixedPoint'`);
* `fixedPointTime C θ L₀ A V p`: an explicit time `T₀ > 0` depending only on the bounds;
* `exists_unique_fixedPoint_of_le_fixedPointTime`: for `0 < T ≤ T₀` and `c = C T^θ` there is a
  unique solution with `‖u‖ ≤ V + 1`;
* `norm_sub_le_of_isFixedPt`: Lipschitz dependence on the datum and on the operators:
  `‖u − u'‖ ≤ (‖v − v'‖ + δ) / (1 − c L)` when `‖𝒦 (F w) − 𝒦' (F' w)‖ ≤ δ` on the ball;
* `eq_of_isFixedPt_of_norm_le`: two solutions of norm `≤ R` coincide once `c L(R) < 1`;
* `le_of_forall_imp_mul_add`: the scalar iteration used for continuity in the model.

**Uniqueness is local.** Uniqueness holds in a ball (or among solutions of norm `≤ R` for
`T ≤ T₀(R)`), not among all solutions: for `X = Y = ℝ`, `𝒦 = c · id`, `F u = u³`, `v = 0` the
equation `u = c u³` has the solutions `± c^{-1/2}` for every `c > 0`. Hairer's uniqueness in all
of `D^{γ,η}_P` on `(0, T)` ("a simple continuity argument") uses the time structure of the
problem (restarting the equation at intermediate times, Proposition 7.11), which the abstract
hypotheses do not contain.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 7.8 and its proof.
-/
@[expose] public noncomputable section
namespace RegularityStructures

end RegularityStructures
end
public section
open Set Function Metric
open scoped NNReal
namespace RegularityStructures
section Scalar

end Scalar
section Banach
variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {𝓚 : Type*}
  [FunLike 𝓚 Y X] [AddMonoidHomClass 𝓚 Y X]
/-- The fixed-point map is `c L`-Lipschitz on a ball where `F` is `L`-Lipschitz. -/
theorem norm_sub_le_of_lipschitz_ball (𝒦 : 𝓚) {c L R : ℝ} (hc : 0 ≤ c)
    (h𝒦 : ∀ y, ‖𝒦 y‖ ≤ c * ‖y‖) {F : X → Y}
    (hF : ∀ u u', ‖u‖ ≤ R → ‖u'‖ ≤ R → ‖F u - F u'‖ ≤ L * ‖u - u'‖) (v : X) {u u' : X}
    (hu : ‖u‖ ≤ R) (hu' : ‖u'‖ ≤ R) :
    ‖(𝒦 (F u) + v) - (𝒦 (F u') + v)‖ ≤ c * L * ‖u - u'‖ := by
  rw [add_sub_add_right_eq_sub, ← map_sub]
  calc ‖𝒦 (F u - F u')‖ ≤ c * ‖F u - F u'‖ := h𝒦 _
    _ ≤ c * (L * ‖u - u'‖) := mul_le_mul_of_nonneg_left (hF u u' hu hu') hc
    _ = c * L * ‖u - u'‖ := by ring

end Banach
end RegularityStructures
end

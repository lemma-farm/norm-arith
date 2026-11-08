-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.DistanceGeometry
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ} {Ω : Opens (Fin n → ℝ)}
/-- The ambient distance is zero exactly on the diagonal
within its domain (BB Prop 1.41, pp. 22–23). -/
theorem DistanceGeometry.distance_eq_zero_iff (G : DistanceGeometry Ω) (x y : Ω) :
    G.d x.val y.val = 0 ↔ x = y := by
  rw [← G.distance_eq]
  exact ⟨G.metric.eq_of_edist_eq_zero,fun h => h ▸ G.metric.edist_self x⟩
theorem DistanceGeometry.continuousOn_distance (G : DistanceGeometry Ω) (x : Ω) :
    ContinuousOn (G.d x.val) (Ω : Set (Fin n → ℝ)) :=
  continuousOn_iff_continuous_domRestrict.mpr (G.continuous_distance x)
/-- Balls are open as subsets of the Euclidean ambient
space, with the original domain condition retained (BB Thm 1.53, p. 35). -/
theorem DistanceGeometry.isOpen_ball (G : DistanceGeometry Ω) (x : Ω) (R : ℝ≥0∞) :
    IsOpen {y : Fin n → ℝ | y ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x.val y < R} := by
  have H := Ω.isOpen.isOpenMap_subtype_val
    {y : Ω | G.d x.val y.val < R} (G.isOpen_ball_subtype x R)
  have he : Subtype.val '' {y : Ω | G.d x.val y.val < R} =
      {y : Fin n → ℝ | y ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x.val y < R} := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.property,hz⟩
    · rintro ⟨hy,hd⟩
      exact ⟨⟨y,hy⟩,hd,rfl⟩
  exact he ▸ H
end RothschildStein.S

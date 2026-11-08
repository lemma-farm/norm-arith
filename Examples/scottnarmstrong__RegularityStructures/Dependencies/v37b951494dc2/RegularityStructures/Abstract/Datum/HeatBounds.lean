/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Abstract.Datum.Deriv
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Derivative bounds from spatial bounds and the heat equation

`HeatLike η A F` packages the properties of a solution `F(t, x) = P_t a(x)` of the heat equation
with `a ∈ 𝒞^η` that are used for the Taylor estimates: `F` is `C^∞` on `{t > 0}`, solves
`∂_t F = ΔF` there, and every spatial derivative of order `m` is bounded by
`K_m A t^{(η - m)/2}` for `0 < t ≤ 1` (`SpatialBound`). The heat equation turns time derivatives
into pairs of spatial ones, so `∂_t^{k₀} ∂_x^β F` is bounded by `K A t^{(η - 2 k₀ - |β|)/2}`
(`HeatLike.bound_D`).
-/
open scoped ContDiff
@[expose] public noncomputable section
namespace RegularityStructures.Datum
/-- The spatial derivative along a word in `{1, 2, 3}` (the coordinate `j : Fin 3` is the
direction `j + 1` of space-time). -/
def pdWord : List (Fin 3) → (ParabolicSpace → ℝ) → ParabolicSpace → ℝ
  | [], F => F
  | j :: w, F => pd j.succ (pdWord w F)
/-- The heat equation `∂_t F = ΔF`. -/
def HeatEq (F : ParabolicSpace → ℝ) : Prop :=
  pd 0 F = ∑ j : Fin 3, pd j.succ (pd j.succ F)
/-- Every spatial derivative of order `m` of every `F i` is `O(A i · t^{(η - m)/2})` for
`0 < t ≤ 1`, with a constant independent of `i`. -/
def SpatialBound {κ : Type*} (η : ℝ) (A : κ → ℝ) (F : κ → ParabolicSpace → ℝ) : Prop :=
  ∀ m : ℕ, ∃ K : ℝ, ∀ (i : κ) (w : List (Fin 3)), w.length = m → ∀ z : ParabolicSpace,
    0 < z.1 → z.1 ≤ 1 → |pdWord w (F i) z| ≤ K * A i * z.1 ^ ((η - m) / 2)
/-- A family of smooth solutions of the heat equation with the spatial bounds of `P_t a`,
`a ∈ 𝒞^η`, `‖a‖_η ≤ A i`, uniformly in the family. -/
structure HeatLike {κ : Type*} (η : ℝ) (A : κ → ℝ) (F : κ → ParabolicSpace → ℝ) : Prop where
  smooth : ∀ i, SmoothPos (F i)
  heat : ∀ i, HeatEq (F i)
  spatial : SpatialBound η A F
end RegularityStructures.Datum
end
public section
open scoped ContDiff
namespace RegularityStructures.Datum
theorem SmoothPos.pdWord {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (w : List (Fin 3)) :
    SmoothPos (RegularityStructures.Datum.pdWord w F) := by
  induction w with
  | nil => exact hF
  | cons j w ih => exact ih.pd _
variable {κ : Type*}
end RegularityStructures.Datum
end

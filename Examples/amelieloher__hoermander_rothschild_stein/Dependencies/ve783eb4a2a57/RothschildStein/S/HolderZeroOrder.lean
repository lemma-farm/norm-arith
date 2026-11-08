-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.HolderBounds
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.Sobolev
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.memHolderX
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.holderXENorm
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
open scoped ENNReal BigOperators
namespace RothschildStein.S
variable {n q : ℕ}
theorem intrinsicWordENorm_nil
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (Ω : Opens (Fin n → ℝ))
    (α : ℝ) (f : (Fin n → ℝ) → ℝ) :
    intrinsicWordENorm X d Ω [] α f = holderENorm d α (Ω : Set (Fin n → ℝ)) f := by
  have hs : {r | ∃ g : (Fin n → ℝ) → ℝ, hasIntrinsicWordDeriv X Ω [] f g ∧
      r = holderENorm d α (Ω : Set (Fin n → ℝ)) g} =
      {holderENorm d α (Ω : Set (Fin n → ℝ)) f} := by
    ext r
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact (holderENorm_congr d α (Ω : Set (Fin n → ℝ)) g hg).symm ▸ mem_singleton _
    · intro hr
      exact ⟨f,fun _ _ => rfl,mem_singleton_iff.mp hr⟩
  unfold intrinsicWordENorm
  rw [hs,sInf_singleton]
end RothschildStein.S

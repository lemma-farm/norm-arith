-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.HolderContinuity
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ}
/-- Restriction retains the original ambient distance and
its Euclidean topology (BB Def 2.13, p. 81; Prop 2.18, p. 84). -/
theorem continuousOn_of_holderENorm_lt_top_subset
    (Ω : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    {V : Set (Fin n → ℝ)} (hV : V ⊆ Ω) {α : ℝ} (hα : 0 < α)
    {f : (Fin n → ℝ) → ℝ} (hf : holderENorm G.d α V f < ⊤) :
    ContinuousOn f V := continuousOn_of_holderENorm_lt_top_on_subset Ω G hV hα hf
end RothschildStein.S

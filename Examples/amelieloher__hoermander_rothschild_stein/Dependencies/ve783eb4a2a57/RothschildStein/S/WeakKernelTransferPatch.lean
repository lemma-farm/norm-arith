-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.WeakRescaledPairing
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.RescaledTransferIdentity
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.CompactKernelDirectionalTest
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.FriedrichsInteriorPatch
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
open Set MeasureTheory Function Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ}
/-- Compact containment of the closure supplies the
positive radius under the local geometric assumptions (BB pp. 75–78; domain). -/
theorem exists_friedrichs_interior_radius
    (Ω : Opens (Fin n → ℝ)) {U : Set (Fin n → ℝ)}
    (hc : IsCompact (closure U)) (hU : closure U ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ cthickening δ (closure U) ⊆ Ω :=
  hc.exists_cthickening_subset_open Ω.isOpen hU
end RothschildStein.S

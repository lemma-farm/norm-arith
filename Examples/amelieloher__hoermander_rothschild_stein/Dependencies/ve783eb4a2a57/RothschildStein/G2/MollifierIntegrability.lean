-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.G2.MollifierScale
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.G2.YoungEndpoint
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
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}
theorem hasCompactSupport_groupRegularize (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) {f : (Fin N → ℝ) → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (groupRegularize G φ f ε) :=
  hasCompactSupport_groupConvolution G (hasCompactSupport_groupMollifierScale G φ hε) hf
end RothschildStein.G2

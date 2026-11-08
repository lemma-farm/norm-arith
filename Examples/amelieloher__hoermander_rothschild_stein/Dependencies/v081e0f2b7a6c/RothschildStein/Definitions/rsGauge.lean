-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.Hormander.Interface.BasisVec
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein
def rsGauge {N : ℕ} (ω : Fin N → ℕ) (_hω : ∀ j, 0 < ω j)
    (u : Fin N → ℝ) : ℝ :=
  sSup (Set.range (fun j => Real.rpow |u j| ((ω j : ℝ)⁻¹)))
end RothschildStein

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.MultiPartial
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.UnitCylinder
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open CKN.Foundation.Parabolic CKN
set_option autoImplicit false
noncomputable section
namespace CIV
/-- The force is bounded in `C²` up to the blow-up time, `eq:interior:force:c-two`. -/
def ForceC2Bounded (f : ParabolicPoint → Vec3) : Prop :=
  ∃ M : ℝ, ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
    |multiPartial (fun w => f w i) α z| ≤ M
end CIV

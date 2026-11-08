-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CKN.Foundation.Parabolic.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CIV
/-- The circulation `Γ = r u_θ = x₁ u₂ - x₂ u₁`. -/
def circulation (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  z.1 0 * u z 1 - z.1 1 * u z 0
end CIV

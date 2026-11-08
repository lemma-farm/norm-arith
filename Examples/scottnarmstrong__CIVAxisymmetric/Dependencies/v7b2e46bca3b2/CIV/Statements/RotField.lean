-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.RotZ
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CIV
/-- The rotated field `(ℛ_φ u)(x, t) = Q_φ u(Q_φ⁻¹ x, t)` of `eq:interior:average`. -/
def rotField (φ : ℝ) (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : Vec3 :=
  rotZ φ (u (rotZ (-φ) z.1, z.2))
end CIV

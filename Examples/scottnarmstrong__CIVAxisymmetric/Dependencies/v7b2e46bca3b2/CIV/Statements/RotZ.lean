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
/-- The rotation `Q_φ` through the angle `φ` about the `z`-axis. -/
def rotZ (φ : ℝ) (x : Vec3) : Vec3 :=
  ![Real.cos φ * x 0 - Real.sin φ * x 1, Real.sin φ * x 0 + Real.cos φ * x 1, x 2]
end CIV

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CKN.Foundation.Parabolic.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
set_option autoImplicit false
open CKN.Foundation.Parabolic
namespace CKN
/-- The open space-time carrier `Ω × I` from paper label `def:sws`. -/
def spaceTimeSet (Ω : Set Vec3) (I : Set ℝ) : Set ParabolicPoint := Ω ×ˢ I
end CKN

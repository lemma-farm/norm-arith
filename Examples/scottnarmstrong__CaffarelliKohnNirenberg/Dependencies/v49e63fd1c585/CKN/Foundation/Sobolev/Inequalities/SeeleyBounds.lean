-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.Seeley
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
/-!
# Quantitative bounds for the two-reflection extension

This file records the derivative and Jacobian estimates on the closed annulus.
The constants are deliberately coarse absolute constants; their role is to
make the change-of-variables estimates explicit.
-/
open Set
open scoped BigOperators
namespace CKN
noncomputable section
attribute [local instance] Classical.propDecidable
end
end CKN

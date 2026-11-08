-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyEnergy
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyC1
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleySplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
/-!
# Gradient energy bounds for the two-reflection extension

The chain rule and the operator-norm estimates from `SeeleyBounds` are
combined with the pullback estimates from `SeeleyEnergy`.
-/
open Set MeasureTheory
open scoped ENNReal
namespace CKN
noncomputable section
attribute [local instance] Classical.propDecidable
end
end CKN

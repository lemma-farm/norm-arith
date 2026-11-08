-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyBounds
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleySplit
set_option autoImplicit false
set_option warningAsError true
/-!
# Change-of-variables energy bounds for the two-reflection extension

The closed-annulus Jacobian lower bounds turn the exact change-of-variables
identities into explicit pullback estimates.  The statements are written for
nonnegative extended-valued integrands, so no auxiliary measurability
assumptions are needed at this stage.
-/
open Set MeasureTheory
open scoped ENNReal
namespace CKN
noncomputable section
attribute [local instance] Classical.propDecidable
end
end CKN

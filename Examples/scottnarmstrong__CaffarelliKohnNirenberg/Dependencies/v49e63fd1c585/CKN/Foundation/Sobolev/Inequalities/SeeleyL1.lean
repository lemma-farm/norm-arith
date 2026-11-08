-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyC1
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyBounds
set_option autoImplicit false
set_option warningAsError true
/-!
# L¹ estimates for the two-reflection extension

These estimates are the endpoint companions of the established quadratic Seeley
energy bounds.  They are used to control the value and derivative terms after
the compactly supported cutoff is applied to a mean-subtracted function.
-/
open Set MeasureTheory
open scoped ENNReal
namespace CKN
noncomputable section
attribute [local instance] Classical.propDecidable
end
end CKN

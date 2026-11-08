-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyC1
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyEnergy
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyGradient
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyPoincare
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyScaling
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.Smooth
set_option autoImplicit false
set_option warningAsError true
/-!
# Unit-ball Sobolev localization through the two-reflection extension

The compactly supported cutoff of the `C¹` extension is the smooth input for the
same-ball estimate.  This module records the localization step explicitly; the
remaining reduction of its outer-ball terms to the original ball is kept separate.
-/
open Set MeasureTheory
open scoped ENNReal
namespace CKN
noncomputable section
attribute [local instance] Classical.propDecidable
end
end CKN

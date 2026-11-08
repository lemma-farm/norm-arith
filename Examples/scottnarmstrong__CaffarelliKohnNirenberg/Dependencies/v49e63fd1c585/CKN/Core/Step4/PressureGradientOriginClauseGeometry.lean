-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.OneSidedMorrey
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientOneSidedCell
set_option autoImplicit false
set_option warningAsError true
/-!
# The backward carrier and the time windows that can contribute to it

The one-sided pressure-gradient estimate of `prop:bootstrap` measures the
selected gradient only through the indicator of the backward cylinder
`parabolicCylinder 0 0 R₁`.  Every cell of that indicator therefore sees the
gradient only on the intersection of the cell with that cylinder, and the time
factor of the intersection is contained in `(-R₁ ^ 2, 0]`, whatever the cell
centre and radius are.

This module records that geometry.  The product decomposition of the
intersection separates the spatial and temporal factors; the window inclusion
says that the contributing times of a cell always lie in the time factor
`(-1, 0]` of the unit cylinder, so a cell bound stated for the intersection
never refers to times outside the region controlled by the data hypothesis of
`thm:A`.  The last theorem is the composition with the one-sided Morrey
transfer: cell bounds for the gradient *restricted to the backward carrier*
give the Morrey cell output the estimate consumes.
-/
open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4

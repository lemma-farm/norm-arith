-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedCell
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedMarginGeometry
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedTwoRegimeMorrey
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientOriginCellProducerSlice
set_option autoImplicit false
set_option warningAsError true
/-!
# The small-cell regime: the slice estimate at twice the cell radius

The slice estimate of display `eq:pressure-gradient-morrey` produces, on a
backward cylinder of radius `ρ` whose closure lies in the space-time domain, a
weak spatial derivative of the pressure slice on the **half** ball of radius
`ρ / 2`.  To control a cell of radius `r` it must therefore be applied at
`ρ = 2 * r`, and this is possible exactly when the doubled cylinder still lies
in the region the hypotheses control.

That is the margin-safe regime.  For the origin carrier the controlled region is
the closed unit cylinder, so the governing condition is `r ≤ (1 - R₁) / 4`, with
a top time in the backward window of the cylinder of admissible centres; for the
symmetric carrier of the uniform route it is `3 * r ≤ R`.  A cell that misses the
carrier
contributes nothing, because the selected field vanishes there, so only cells
meeting the carrier have to be considered, and for those the margin condition is
what makes the doubled ball fit.

Cells above the margin scale are **not** reached by this argument; they belong to
the other regime and are bounded by the whole-carrier integral.
-/
open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4

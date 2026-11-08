-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedSlice
set_option autoImplicit false
set_option warningAsError true
/-!
# The slice bound of one field at every cell scale

A cell estimate for the parabolic Morrey class needs the radius factor
`r ^ (5 * (1 - P / κ))`, which a slice bound at one fixed scale cannot produce:
one ball's slice bound, integrated in time, carries no decay in the cell
radius.  What does produce it is the slice estimate applied at each cell's own
radius.

The statement below performs that transfer for one fixed space-time field.  The
field is tied to the pressure by being a weak spatial derivative on a common
open carrier at almost every time of the cell's window; the cell datum is a
slice bound for *some* weak spatial derivative on the cell's own ball.  Almost
everywhere uniqueness of weak partial derivatives then transports the cell's
bound to the one field.  Its conclusion is exactly the slice hypothesis of the
time integration that turns slice bounds into the cell power integral.
-/
open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedUnion
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedGeometry
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Statements.SpaceTimeSet
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Cutoff.Ball
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
set_option autoImplicit false
set_option warningAsError true
/-!
# The spatial gradient of a pressure slice on a whole ball

Display (3.5) produces, on a backward cylinder of radius `ρ`, a weak spatial
gradient of the pressure slice only on the concentric ball of radius `ρ / 2`,
and the radius `ρ` is limited by the time window that the cylinder must fit
into.  A single application therefore never reaches a prescribed ball.

Applying it instead on every sufficiently small cylinder of a fixed countable
family and gluing the outcomes reaches every ball whose closure stays inside
the spatial domain, at almost every time of the whole time set.  The gluing is
`exists_weakPartialDerivOn_of_local`; the countable family comes from a
countable dense set of centres together with rational radii and rational top
times, so that the almost-everywhere conditions can be intersected.

Because a locally integrable weak partial derivative is unique almost
everywhere on an open set, every bound proved for a slice gradient on a
sub-ball is inherited by the glued field there.  That is the mechanism that
makes a bound available at *every* cell scale rather than at one scale only.
-/
open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4

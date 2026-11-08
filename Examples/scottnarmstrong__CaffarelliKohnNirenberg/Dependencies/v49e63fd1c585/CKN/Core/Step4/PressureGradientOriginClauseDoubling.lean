-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientOriginClauseBounds
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedSmallCell
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientOriginCellInstanceQuantitative
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientOriginCellInstanceMeasurable
set_option autoImplicit false
set_option warningAsError true
/-!
# Doubled source cylinders for clipped origin cells

The pressure slice estimate on a cylinder of radius `2 * r` controls its
half-ball of radius `r`. Weak derivative uniqueness on the intersection with
the origin carrier transfers that bound to a field defined only on the
carrier ball. The resulting time integral uses the clipped cell window.
For centres in the closed origin cylinder, this construction is admissible
through radius `(1 - R₁) / 2`, twice the origin margin scale.
-/
open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4

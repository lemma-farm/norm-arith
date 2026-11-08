-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Setting.Finiteness
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Integration.Average
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
/-!
# Fubini steps for the cylinder quantities of `prop:lin34`

The cylinder quantities `D(z,r)` and `Ĉ(z,ρ)` of `eq:Chat` in `paper/ckn.tex`
are defined as integrals over a parabolic cylinder, while the monotonicity and
scaling statements of `prop:lin34` are phrased in terms of the spatial slice
quantities obtained by fixing the time variable.  This file records the two
Fubini facts that pass between the two points of view.

The cylinder `parabolicCylinder x t r` is the product `vec3Ball x r ×ˢ Ioc (t - r ^ 2) t`
and the volume on `ParabolicPoint` is the product of the spatial and time
volumes, so an integrability hypothesis over the cylinder is an integrability
hypothesis for the product measure.  Applying the Fubini API with the time
variable as the outer variable then yields the integrability of the time slices.
-/
end CKN

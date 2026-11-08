-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationExtensionUnconditional
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Lin34CentredSource
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Lin34SliceIntegrated
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
open CKN.Foundation.Euclidean
/-!
# The Calderón--Zygmund bound for the centred first pressure potential

The oscillation estimate `prop:lin34` of `paper/ckn.tex` consumes the external
input `ext:CZ` in the shape

`‖p₁(·, s)‖_{L^{3/2}(ℝ³)} ≤ C₁₁ · (∫_{B_ρ} |u - ⨍u|³)^{2/3}`,

where `p₁` is the leading potential of `prop:pressure-decomposition` run with
the doubly centred nonlinearity `eq:Uhat`.  This file derives that display from
the unconditional singular-integral estimate for the indexed second-order Riesz
extension, the source estimate for the cut-off centred tensor, and the
distributional identification data for the centred potential.
-/
end CKN

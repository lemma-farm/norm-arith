-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.WeakPressureSlice
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientSlice
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.BallDisplays
set_option autoImplicit false
set_option warningAsError true
/-! # Slice-selected pressure gradients: classical, additive, quantitative forms

Display (3.5) of the pressure-gradient section selects, on a half ball, the
coordinate weak derivative of the pressure obtained by splitting it into a
particular potential and a smooth harmonic representative.  The ingredients
recorded here are exactly the ones that selection step consumes: a `C¹`
function has its classical coordinate gradient as a weak partial derivative,
weak partial derivatives add along an a.e. decomposition of the carrier, and a
coordinate field obeying a pointwise gradient display is controlled in `L^(6/5)`
on the half ball. -/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4

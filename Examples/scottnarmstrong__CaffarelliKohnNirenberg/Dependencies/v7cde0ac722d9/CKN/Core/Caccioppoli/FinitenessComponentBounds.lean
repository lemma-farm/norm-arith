-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Setting.InterpolationBall
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Setting.InterpolationCylinder
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Setting.SobolevPoincareBridge
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Setting.Finiteness
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Pressure.SliceIntegrability
set_option autoImplicit false
set_option warningAsError true
/-! Componentwise norm estimates used by Caccioppoli finiteness arguments. -/
open MeasureTheory Set Filter CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN

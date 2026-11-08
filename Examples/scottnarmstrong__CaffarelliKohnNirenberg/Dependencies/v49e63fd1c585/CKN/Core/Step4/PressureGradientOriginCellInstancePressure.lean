-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientOriginCellInstanceAssembly
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedSlice
set_option autoImplicit false
set_option warningAsError true
/-!
# Pressure slices on the whole solution interval

The local pressure integrability of a suitable weak solution supplies the
pressure premise of spatial weak-gradient gluing in `prop:bootstrap`.
A compact exhaustion of the time interval makes the exceptional set uniform
on the entire interval.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
open OriginInstance
end CKN.Core.Step4

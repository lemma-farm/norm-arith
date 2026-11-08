-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.HeatPotential.SubordinatedFar
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step3.LocalizedEquationDuhamel
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Morrey.Minkowski
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential
open CKN.Core.Step3
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
/-! Product estimates used by the divergence-form sources.  The cutoff
factors are deliberately represented by their finite Morrey norms here; the
smooth compact-support cutoff API supplies those bounds at the point where a
cutoff is chosen. -/
end CKN.Core.Step4

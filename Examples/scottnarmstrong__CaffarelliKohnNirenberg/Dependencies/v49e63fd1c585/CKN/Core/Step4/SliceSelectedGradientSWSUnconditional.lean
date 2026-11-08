-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradient
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientIdentification
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientRegularity
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientForceUnconditional
set_option autoImplicit false
set_option warningAsError true
/-! # Display (3.5) on a slice, with no condition on the divergence of the force

Display (3.5) of the pressure-gradient section selects, for almost every time
of the one-sided interval `J_ρ`, a weak spatial gradient of the pressure slice
on the half ball `B_{ρ/2}(x₀)` together with its `L^{6/5}` bound.  The general
form of that selection carries three analytic hypotheses: the interior
regularity of the harmonic part of the local pressure decomposition, the
first-order identification of the first pressure potential, and the weak
gradient of the two force potentials.

The class `def:sws` imposes no condition on the spatial divergence of the
force, so the two force potentials of `eq:pk` do not cancel and the display
must carry them.  This file discharges the first hypothesis outright, reduces
the second to the divergence-form characterization of the slice source `V`, and
discharges the third from the force data of the solution alone: the bound
gains the `ρ^{-1/2}`-weighted force term `sliceForceGradientBound`.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Lin34SliceHolder
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.OscillationLin34Solution
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Harmonic.InteriorEstimatesBasic
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN
/-!
# The centred pressure decomposition on one time slice

This file runs the local pressure decomposition of `prop:pressure-decomposition`
(`paper/ckn.tex`) with the doubly centred nonlinearity `eq:Uhat` of
`lem:delta-p-centred` in place of the raw one, which is the form the oscillation
estimate `prop:lin34` uses: the velocity then enters only through the mean-free
field `u - ⨍_{B_ρ} u` of `eq:Chat`.
-/
end CKN

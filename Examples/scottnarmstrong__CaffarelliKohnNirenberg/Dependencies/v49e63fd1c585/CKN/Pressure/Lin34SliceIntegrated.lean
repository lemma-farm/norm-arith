-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Lin34SliceForceLp
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Lin34SliceQuantities
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
# `eq:lin34-pointwise` for a suitable weak solution, and its time integral

This file discharges, for a suitable weak solution, every hypothesis of the
integrated estimate `eq:lin35-force` of `prop:lin34`(ii-b) in `paper/ckn.tex`
except the Calderón--Zygmund bound `ext:CZ` for the centred first potential,
which stays named as `hCZ_p1`.
-/
end CKN

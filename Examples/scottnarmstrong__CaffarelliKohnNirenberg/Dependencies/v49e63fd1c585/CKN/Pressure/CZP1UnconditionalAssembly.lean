-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationCZP1Unconditional
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationExtensionUnconditional
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Lin34CentredCZ
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.SliceVelocityCube
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
# Unconditional Calderón--Zygmund input assemblies

The endpoint singular-integral estimate is a fixed-time statement.  This file
performs the solution-level assembly for the singly centred pressure field
consumed by the theta-decay cylinder bridge.
-/
/- The source producer supplies the nine tensor components directly from the
   suitable-solution slice bounds.  Its `27` majorant is exactly the nine-entry
   sum in the endpoint estimate, hence the displayed pressure constant is
   `9 * C_CZ`. -/
end CKN

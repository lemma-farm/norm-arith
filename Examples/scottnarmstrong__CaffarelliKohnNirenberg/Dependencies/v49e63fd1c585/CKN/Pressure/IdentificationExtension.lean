-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationWholeSpace
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PotentialDecay
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.LpExtensionCZ
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.TensorExtensionPairing
set_option autoImplicit false
set_option warningAsError true
/-!
# Indexed pressure-extension identification

The global pressure operator in this file is the indexed `L^(3/2)` extension.
The ordinary Newtonian kernel expression is an exterior tail object and is not
used by the global identification.
-/
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
open CKN.Foundation.Euclidean
end CKN

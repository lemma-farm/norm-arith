-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelUnitBound
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
set_option autoImplicit false
set_option warningAsError true
/-!
# Parabolic scaling for multiplier heat kernels
-/
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat
end CKN.Foundation.Euclidean

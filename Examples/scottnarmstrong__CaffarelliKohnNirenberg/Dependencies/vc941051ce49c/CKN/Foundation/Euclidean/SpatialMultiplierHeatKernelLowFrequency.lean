-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelHighFrequencyFourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
set_option autoImplicit false
set_option warningAsError true
/-!
# Compact-frequency bounds for homogeneous multiplier kernels
-/
open scoped BigOperators FourierTransform
open MeasureTheory Set
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier
end CKN.Foundation.Euclidean

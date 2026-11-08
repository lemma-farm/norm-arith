-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelTimeDerivative
set_option autoImplicit false
set_option warningAsError true
/-!
# Bounds for degree-one multiplier heat kernels

The frequency representation gives the size, spatial-gradient, and time-derivative
bounds for every smooth degree-one symbol, with one symbol-dependent constant.
-/
open scoped BigOperators
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat
end CKN.Foundation.Euclidean

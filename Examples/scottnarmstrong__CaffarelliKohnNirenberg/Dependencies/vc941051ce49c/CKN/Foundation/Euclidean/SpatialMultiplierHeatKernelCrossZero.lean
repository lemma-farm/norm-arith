-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelLocalIntegrable
set_option autoImplicit false
set_option warningAsError true
/-!
# Cross-zero estimates for multiplier heat kernels

The kernel value and spatial gradient satisfy their parabolic bounds on the
whole time axis. Its time derivative bound is extended to nonzero times.
-/
open scoped BigOperators Topology
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat
end CKN.Foundation.Euclidean

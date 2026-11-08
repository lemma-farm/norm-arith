-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Euclidean.SpatialMultiplierKernel
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Core.HeatPotential.Kernel
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators
open MeasureTheory
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Euclidean
open CKN.Foundation.Heat CKN.Foundation.Parabolic
/-! The finite general-symbol heat potential used in the heat-kernel family.

This is the potential from `eq:heat-potential` in `paper/ckn.tex`, with the
real-valued source data paired against the complex-valued causal kernels.
-/
end CKN.Core.HeatPotential

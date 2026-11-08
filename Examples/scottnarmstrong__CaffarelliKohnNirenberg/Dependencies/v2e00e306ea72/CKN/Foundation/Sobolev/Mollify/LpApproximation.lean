-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Mollify.LpConvolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Mollify.SupportThickening
set_option autoImplicit false
set_option warningAsError true
/-!
# Global and local `Lᵖ` approximation by mollification

The three results below separate translation continuity, the normalized-kernel
estimate, and the compact-localization step used for interior convergence.
-/
open Function Set Filter MeasureTheory Topology
open scoped ENNReal Convolution Pointwise
namespace CKN
noncomputable section
end
end CKN

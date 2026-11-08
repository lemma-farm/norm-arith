-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelSpatialDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
set_option autoImplicit false
set_option warningAsError true
/-!
# Time differentiability of multiplier heat kernels
-/
open scoped BigOperators
open MeasureTheory
open Filter
open TopologicalSpace
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat
end CKN.Foundation.Euclidean

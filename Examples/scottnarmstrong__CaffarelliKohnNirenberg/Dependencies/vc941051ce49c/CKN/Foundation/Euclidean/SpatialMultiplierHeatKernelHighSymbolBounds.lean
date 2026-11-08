-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelBounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Fourier.FourierTransformDeriv
set_option autoImplicit false
set_option warningAsError true
/-!
# High-frequency symbol estimates
-/
open scoped BigOperators
open Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat
end CKN.Foundation.Euclidean

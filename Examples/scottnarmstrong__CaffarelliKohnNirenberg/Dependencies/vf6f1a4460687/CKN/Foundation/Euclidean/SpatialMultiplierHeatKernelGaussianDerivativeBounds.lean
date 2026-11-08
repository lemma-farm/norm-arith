-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelHighSymbolBounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Fourier.FourierTransformDeriv
set_option autoImplicit false
set_option warningAsError true
/-!
# Derivative bounds for the frequency Gaussian
-/
open scoped BigOperators
open Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat
end CKN.Foundation.Euclidean

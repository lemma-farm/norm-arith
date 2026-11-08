-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelBounds
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelHighSymbolBounds
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelGaussianDerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
set_option autoImplicit false
set_option warningAsError true
/-!
# Fourier estimates for the spatial multiplier heat kernel

This module proves the pointwise estimates for smooth degree-one homogeneous
frequency symbols by cutting off the origin and integrating by parts in the
Fourier variable.
-/
open scoped BigOperators
open scoped FourierTransform
open Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier
end CKN.Foundation.Euclidean

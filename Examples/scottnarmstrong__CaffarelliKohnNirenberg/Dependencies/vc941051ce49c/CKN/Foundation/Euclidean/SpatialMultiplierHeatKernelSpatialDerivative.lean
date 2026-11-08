-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelScaling
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Sobolev.Ambient.Basis
import Mathlib.Analysis.Fourier.FourierTransformDeriv
set_option autoImplicit false
set_option warningAsError true
/-!
# Spatial differentiability of multiplier heat kernels
-/
open scoped BigOperators FourierTransform
open MeasureTheory
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier
end CKN.Foundation.Euclidean

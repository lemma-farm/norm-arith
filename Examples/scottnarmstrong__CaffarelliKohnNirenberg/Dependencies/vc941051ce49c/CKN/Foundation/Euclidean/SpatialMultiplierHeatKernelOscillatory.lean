-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelBoundsProof
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
set_option autoImplicit false
set_option warningAsError true
/-!
# Oscillatory estimates for homogeneous multiplier kernels

This module develops the integration-by-parts estimates for the smooth
high-frequency part of a homogeneous multiplier.
-/
open scoped BigOperators
open MeasureTheory Set Module
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier
end CKN.Foundation.Euclidean

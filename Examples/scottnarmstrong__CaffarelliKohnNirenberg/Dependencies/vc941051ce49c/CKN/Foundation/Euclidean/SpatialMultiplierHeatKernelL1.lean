-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelOscillatory
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
set_option autoImplicit false
set_option warningAsError true
/-!
# Uniform integrability estimates for damped homogeneous symbols
-/
open scoped BigOperators
open MeasureTheory Set Module
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier
end CKN.Foundation.Euclidean

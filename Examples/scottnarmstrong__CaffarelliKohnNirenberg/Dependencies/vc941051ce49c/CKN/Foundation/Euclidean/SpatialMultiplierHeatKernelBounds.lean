-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Euclidean.SpatialMultiplierKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Fourier.FourierTransformDeriv
set_option autoImplicit false
set_option warningAsError true
/-!
# Bounds for the spatial multiplier heat kernel

The multiplier clauses of equation `eq:heat-kernel-bounds` in the proof of
Proposition `prop:heat-morrey-hoelder` are the pointwise bounds for a smooth,
degree-one homogeneous spatial Fourier symbol applied to the forward heat
kernel.  The paper passage is `paper/ckn.tex`, label `eq:heat-kernel-bounds`.
-/
open scoped BigOperators
open Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic CKN.Foundation.Heat
end CKN.Foundation.Euclidean

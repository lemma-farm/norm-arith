-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Morrey.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Integration.ProdSwap
set_option autoImplicit false
set_option warningAsError true
/-!
# Product-box power integrals and their spatial slices

This module records the product-box form of the slice decomposition of a power
integral.  For a nonnegative function on `Vec3 × ℝ` and arbitrary sets `E` of
space points and `F` of times, the integral of the power `|g| ^ P` over the box
`E ×ˢ F` equals the integral over `F` of the spatial power integrals of the
slices `y ↦ g (y, s)`.

The second result turns an almost-everywhere bound on the `L^P` norm of the
spatial slices into a bound on the power integral over the whole box.  Both are
stated for an arbitrary spatial set and an arbitrary time set; no geometry of a
ball or a backward time window is used.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4

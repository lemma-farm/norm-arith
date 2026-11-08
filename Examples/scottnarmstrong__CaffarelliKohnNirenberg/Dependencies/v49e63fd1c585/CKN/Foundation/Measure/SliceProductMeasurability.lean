-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Ambient.Basic
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
set_option warningAsError true
/-!
# Sliced convolution integrals and product-measure slicing

Two measure-theoretic facts used when a family of spatial statements indexed by
time, such as the slice-wise pressure equation of `lem:delta-p`, is assembled
into a single space-time statement.

* `stronglyMeasurable_slice_kernel_integral`: convolving a jointly measurable
  space-time integrand with a continuous kernel in the space variable alone
  produces a jointly measurable function of the space-time point.

* `ae_ae_of_ae_prod_snd` and `ae_prod_of_ae_ae_snd`: the two directions relating
  a product-almost-everywhere statement to its iterated form sliced in the
  *second* factor, which is the time factor in the product carrier `Vec3 × ℝ`.
  Mathlib states these for slices in the first factor; the versions here are
  obtained by transporting along the measure-preserving coordinate swap.
-/
open MeasureTheory MeasureTheory.Measure
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
end

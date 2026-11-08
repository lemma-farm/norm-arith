-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Harmonic.KernelAllOrdersSphere
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators Topology
open MeasureTheory
open CKN.Foundation.Parabolic
set_option autoImplicit false
/-!
# Shifted kernels: measurability and separation

A kernel continuous away from the origin gives a measurable shifted integrand,
because the shifted singularity is a single point and hence a null set.  The
remaining lemmas record the reflection symmetry of the Euclidean length, the
fact that a small sup-norm displacement loses at most half of a Euclidean
separation, and the monotonicity of inverse powers.  These support the
potential estimates of `cor:CZ-harmonic`.
-/
noncomputable section
namespace CKN.Foundation.Heat
end CKN.Foundation.Heat

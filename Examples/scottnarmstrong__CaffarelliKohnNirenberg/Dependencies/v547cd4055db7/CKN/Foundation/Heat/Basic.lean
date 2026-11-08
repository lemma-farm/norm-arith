-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Parabolic.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
set_option warningAsError true
/-!
# The three-dimensional heat kernel

This file fixes the Gaussian normalization used by the parabolic estimates.
The spatial variable is the repository's `Fin 3 → ℝ` type, and the spatial
quadratic form is written as a finite sum so that it is independent of the
ambient sup norm on the function space.
-/
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
open CKN.Foundation.Parabolic
/-! ### Definitions and elementary identities -/
end CKN.Foundation.Heat

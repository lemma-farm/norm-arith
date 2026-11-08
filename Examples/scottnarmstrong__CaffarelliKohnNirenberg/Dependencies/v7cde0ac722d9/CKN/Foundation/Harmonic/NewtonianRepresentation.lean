-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Harmonic.Newtonian
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology Interval
open MeasureTheory MeasureTheory.Measure Set Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
open CKN.Foundation.Parabolic
/-! The Newtonian kernel representation obtained from the heat semigroup. -/
/-- The positive three-dimensional Newtonian kernel. -/
def newtonianKernel (z : Vec3) : ℝ :=
  1 / (4 * Real.pi * vec3EuclideanNorm z)
end CKN.Foundation.Heat

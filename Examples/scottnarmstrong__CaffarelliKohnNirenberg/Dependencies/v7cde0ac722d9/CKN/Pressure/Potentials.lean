-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Harmonic.Interior
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Harmonic.NewtonianKernelIntegrability
import Mathlib.Analysis.Calculus.FDeriv.Measurable
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN
def pressureNewtonianPotential (g : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∫ y, (-newtonianKernel (x-y)) * g y
/-- The first derivative potential, written as `-∂ⱼN * g = ∂ⱼ(newtonianKernel) * g`. -/
def pressureNewtonianDerivativePotential (i : Fin 3) (g : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∫ y, CKN.spatialDeriv newtonianKernel i (x-y) * g y
end CKN

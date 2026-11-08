-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Decomposition
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.DerivativeAdjoint
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN
/-! The eight explicit potentials in the local pressure decomposition. -/
def pressureP2 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) : Vec3 → ℝ := fun x =>
  ∑ i, ∑ j, pressureNewtonianPotential
    (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x
def pressureP3 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) : Vec3 → ℝ := fun x =>
  ∑ i, ∑ j, pressureNewtonianDerivativePotential j
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x
def pressureP4 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) : Vec3 → ℝ := fun x =>
  ∑ i, ∑ j, pressureNewtonianDerivativePotential i
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x
def pressureP5 (η : Vec3 → ℝ) (p : ParabolicPoint → ℝ) (s : ℝ) : Vec3 → ℝ := fun x =>
  -pressureNewtonianPotential (fun y => p (y, s) * spatialLaplacian η y) x
def pressureP6 (η : Vec3 → ℝ) (p : ParabolicPoint → ℝ) (s : ℝ) : Vec3 → ℝ := fun x =>
  -2 * ∑ j, pressureNewtonianDerivativePotential j
    (fun y => spatialDeriv η j y * p (y, s)) x
def pressureP7 (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) : Vec3 → ℝ := fun x =>
  -∑ j, pressureNewtonianDerivativePotential j
    (fun y => η y * f (y, s) j) x
def pressureP8 (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) : Vec3 → ℝ := fun x =>
  -∑ j, pressureNewtonianPotential
    (fun y => spatialDeriv η j y * f (y, s) j) x
end CKN

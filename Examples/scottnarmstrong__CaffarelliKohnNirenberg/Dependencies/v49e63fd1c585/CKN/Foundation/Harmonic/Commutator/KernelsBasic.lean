-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Cutoff.Ball
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.LeibnizLaplacian
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators Topology
open Filter MeasureTheory
namespace CKN.Foundation.Harmonic.Commutator
noncomputable section
private def q (x : CKN.Vec 3) : ℝ := CKN.vecNormSq x
def inverseThirdFormula (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -15 * x m * x j * x l * (CKN.vecEuclideanNorm x ^ 7)⁻¹ +
    3 * ((if m = l then 1 else 0) * x j +
      (if m = j then 1 else 0) * x l +
      (if l = j then 1 else 0) * x m) *
      (CKN.vecEuclideanNorm x ^ 5)⁻¹
def newtonianKernel (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -(4 * Real.pi)⁻¹ * inverseThirdFormula m j l x
end
end CKN.Foundation.Harmonic.Commutator

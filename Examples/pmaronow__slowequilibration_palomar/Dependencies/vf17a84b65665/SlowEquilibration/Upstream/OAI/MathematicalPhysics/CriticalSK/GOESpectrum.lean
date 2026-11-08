-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.Upstream.OAI.MathematicalPhysics.CriticalSK.GaussianMatrices
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.Upstream.OAI.MathematicalPhysics.CriticalSK.Resolvent
set_option autoImplicit false
@[expose] public section
namespace OAI
noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open scoped BigOperators InnerProductSpace
open Module
open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open scoped BigOperators
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
namespace CriticalSK
open scoped InnerProductSpace
def gaussianMatrixCLM {n : ℕ} (A : GaussianMatrix (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toLpLin 2 2 (fun i j => A i j)).toContinuousLinearMap
lemma gaussianMatrixCLM_symmetric {n : ℕ} (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) : (gaussianMatrixCLM A).toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  exact hA j i
lemma symmetrize_half_entry {n : ℕ} (A : GaussianMatrix (Fin n)) (i j : Fin n) :
    symmetrizeGaussianMatrix (1/2:ℝ) A i j = (A i j + A j i)/2 := by
  change (1/2:ℝ)*(A i j+A j i) = _
  ring
lemma symmetrize_half_symmetric {n : ℕ} (A : GaussianMatrix (Fin n)) :
    ∀ i j, symmetrizeGaussianMatrix (1/2:ℝ) A i j = symmetrizeGaussianMatrix (1/2:ℝ) A j i := by
  intro i j
  rw [symmetrize_half_entry,symmetrize_half_entry,add_comm]
def matrixOrderedEigenvalues {n : ℕ} (A : GaussianMatrix (Fin n)) : Fin n → ℝ :=
  (gaussianMatrixCLM_symmetric _ (symmetrize_half_symmetric A)).eigenvalues (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)
def triEntriesLaw (n : ℕ) (s : ℝ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi fun i => (gaussianReal 0 (4*s^2).toNNReal).prod (columnNormLaw (n-i.val-1) s)
instance triEntriesLaw_probability (n : ℕ) (s : ℝ) : IsProbabilityMeasure (triEntriesLaw n s) := by
  unfold triEntriesLaw; infer_instance
def goeScale (n : ℕ) : ℝ := (Real.sqrt (2*(n+1:ℝ)))⁻¹
end CriticalSK
end
end OAI

module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v034b2acfdab0.GinibrePoincare.Analysis.MatrixGaussianLSI
@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev MatrixRealSpace (n : ℕ) := Fin n → Fin n → ℂ
def matrixSpatialBump (n : ℕ) : ContDiffBump (0 : MatrixRealSpace n) :=
  ⟨1, 2, by norm_num, by norm_num⟩
def matrixSpatialCutoff (n k : ℕ) (A : MatrixRealSpace n) : ℝ :=
  matrixSpatialBump n (((k : ℝ) + 1)⁻¹ • A)
theorem matrixSpatialCutoff_fderiv (n k : ℕ) (A H : MatrixRealSpace n) :
    fderiv ℝ (matrixSpatialCutoff n k) A H =
      ((k : ℝ) + 1)⁻¹ * fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
        (((k : ℝ) + 1)⁻¹ • A) H := by
  have hd := (((matrixSpatialBump n).contDiff (n := 1)).differentiable (by norm_num)
    (((k : ℝ) + 1)⁻¹ • A)).hasFDerivAt.comp A
      ((hasFDerivAt_id A).const_smul (((k : ℝ) + 1)⁻¹))
  unfold matrixSpatialCutoff
  simpa [matrixSpatialCutoff, Function.comp_def, ContinuousLinearMap.comp_apply,
    map_smul, smul_eq_mul] using congrArg (fun L : MatrixRealSpace n →L[ℝ] ℝ => L H) hd.fderiv
#print axioms matrixSpatialCutoff_fderiv
theorem matrixSpatialCutoff_derivative_bound (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k (A H : MatrixRealSpace n),
      |fderiv ℝ (matrixSpatialCutoff n k) A H| ≤ M / ((k : ℝ) + 1) * ‖H‖ := by
  obtain ⟨M, hM⟩ := ((matrixSpatialBump n).contDiff (n := 1)).continuous_fderiv one_ne_zero
    |>.bounded_above_of_compact_support ((matrixSpatialBump n).hasCompactSupport.fderiv ℝ)
  refine ⟨M, (norm_nonneg _).trans (hM 0), ?_⟩
  intro k A H
  rw [matrixSpatialCutoff_fderiv, abs_mul, abs_of_nonneg (by positivity)]
  have hnorm := (fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
    (((k : ℝ) + 1)⁻¹ • A)).le_opNorm H
  have hh : |fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
      (((k : ℝ) + 1)⁻¹ • A) H| ≤ M * ‖H‖ :=
    hnorm.trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg H))
  calc
    _ ≤ ((k : ℝ) + 1)⁻¹ * (M * ‖H‖) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring
end
end GinibrePoincare

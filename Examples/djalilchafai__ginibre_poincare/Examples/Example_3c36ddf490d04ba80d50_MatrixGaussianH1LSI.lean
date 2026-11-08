module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v75fdf4fabb72.GinibrePoincare.Analysis.MatrixSpatialCutoff
@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
def matrixSpatialTruncation (n k : ℕ) (F : MatrixRealSpace n → ℝ) : MatrixRealSpace n → ℝ :=
  fun A => matrixSpatialCutoff n k A * F A
theorem matrixSpatialTruncation_contDiff (n k : ℕ) (F : MatrixRealSpace n → ℝ)
    (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (matrixSpatialTruncation n k F) :=
  ((matrixSpatialCutoff_smooth n k).of_le (by simp)).mul hF
theorem matrixSpatialTruncation_fderiv (n k : ℕ) (F : MatrixRealSpace n → ℝ)
    (hF : ContDiff ℝ 1 F) (A H : MatrixRealSpace n) :
    fderiv ℝ (matrixSpatialTruncation n k F) A H =
      fderiv ℝ (matrixSpatialCutoff n k) A H * F A +
        matrixSpatialCutoff n k A * fderiv ℝ F A H := by
  have hd := ((matrixSpatialCutoff_smooth n k).differentiable (by simp) A).hasFDerivAt.mul
    (hF.differentiable (by norm_num) A).hasFDerivAt
  unfold matrixSpatialTruncation
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, mul_comm, add_comm, Pi.mul_def] using
      congrArg (fun L : MatrixRealSpace n →L[ℝ] ℝ => L H) hd.fderiv
theorem matrixSpatialTruncation_limits (n : ℕ) (F : MatrixRealSpace n → ℝ)
    (hF : ContDiff ℝ 1 F) (A H : MatrixRealSpace n) :
    Tendsto (fun k => matrixSpatialTruncation n k F A) atTop (nhds (F A)) ∧
      Tendsto (fun k => fderiv ℝ (matrixSpatialTruncation n k F) A H)
        atTop (nhds (fderiv ℝ F A H)) := by
  constructor
  · simpa [matrixSpatialTruncation] using (matrixSpatialCutoff_tendsto n A).mul_const (F A)
  · simp_rw [matrixSpatialTruncation_fderiv n _ F hF A H]
    simpa using ((matrixSpatialCutoff_derivative_tendsto n A H).mul_const (F A)).add
      ((matrixSpatialCutoff_tendsto n A).mul_const (fderiv ℝ F A H))
theorem matrixSpatialTruncation_mass_tendsto (n : ℕ) (μ : Measure (MatrixRealSpace n))
    (F : MatrixRealSpace n → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ) :
    Tendsto (fun k => ∫ A, matrixSpatialTruncation n k F A ^ 2 ∂μ)
      atTop (nhds (∫ A, F A ^ 2 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun A => F A ^ 2)
    (fun k => ((matrixSpatialTruncation_contDiff n k F hF).continuous.pow 2).aestronglyMeasurable)
    hv.integrable_sq
  · intro k
    apply ae_of_all
    intro A
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h0, h1⟩ := matrixSpatialCutoff_mem_unit n k A
    change (matrixSpatialCutoff n k A * F A) ^ 2 ≤ F A ^ 2
    have hc : matrixSpatialCutoff n k A ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (F A))]
  · exact ae_of_all _ fun A => ((matrixSpatialTruncation_limits n F hF A 0).1).pow 2
#print axioms matrixSpatialTruncation_mass_tendsto
end
end GinibrePoincare

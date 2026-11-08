module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.OrthogonalSplitting
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.BipartiteEnergy
@[expose] public section
/-!
# Right singular truncation

The retained right space is constructed from the spectral theorem for the
Gram matrix. This works for rectangular matrices, including empty dimensions.
All matrix norms in this module are Euclidean operator norms.
-/
namespace KKPAsymptotic
open Matrix Unitary
open scoped Classical Matrix.Norms.L2Operator
variable {H R : Type*} [Fintype H] [DecidableEq H] [Fintype R] [DecidableEq R]
/-- Diagonal functional calculus in the fixed orthonormal eigenbasis. -/
noncomputable def spectralMap {C : Matrix R R ℝ} (hC : C.IsHermitian)
    (f : ℝ → ℝ) : Matrix R R ℝ :=
  conjStarAlgAut ℝ (Matrix R R ℝ) hC.eigenvectorUnitary
    (diagonal (fun i => f (hC.eigenvalues i)))
theorem spectralMap_id {C : Matrix R R ℝ} (hC : C.IsHermitian) :
    spectralMap hC id = C := by
  simpa [spectralMap, Function.comp_def] using hC.spectral_theorem.symm
theorem spectralMap_norm_le {C : Matrix R R ℝ} (hC : C.IsHermitian)
    (f : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ i, |f (hC.eigenvalues i)| ≤ c) : ‖spectralMap hC f‖ ≤ c := by
  simp only [spectralMap, conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hc).mpr (fun i => by simpa using hf i)
omit [DecidableEq H] in
/-- The Euclidean operator norm is bounded by the Frobenius mass, for rectangular matrices. -/
theorem rectangular_opNorm_sq_le (B : Matrix H R ℝ) :
    ‖B‖ ^ 2 ≤ ∑ i : H, ∑ j : R, B i j ^ 2 := by
  let C := Bᴴ * B
  have hC : C.PosSemidef := posSemidef_conjTranspose_mul_self B
  have ht : C.trace = ∑ i : H, ∑ j : R, B i j ^ 2 := by
    simp only [C, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      conjTranspose_eq_transpose_of_trivial, transpose_apply, ← pow_two]
    exact Finset.sum_comm
  have hn : ‖C‖ ≤ C.trace := by
    conv_lhs => rw [← spectralMap_id hC.isHermitian]
    apply spectralMap_norm_le hC.isHermitian id hC.trace_nonneg
    intro i
    simp only [id_eq, abs_of_nonneg (hC.eigenvalues_nonneg i)]
    rw [hC.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hC.eigenvalues_nonneg j) (Finset.mem_univ i)
  change ‖Bᴴ * B‖ ≤ _ at hn
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, ht] at hn
  simpa only [pow_two] using hn
end KKPAsymptotic

/-
# Von Neumann's inequality (L4.1)

For a contraction `T` on a complex Hilbert space `E` and a polynomial `p`,
`‖p(T)‖ ≤ sup_{‖z‖ ≤ 1} ‖p(z)‖`.

Route (task-spec L4.1, via dilation): the Schäffer dilation (L3.1) gives a Hilbert space `H`,
an inner-product-preserving `V : E →L[ℂ] H` and a unitary `U` on `H` with
`V† U^n V = T^n` for all `n`. Then

1. `V† p(U) V = p(T)` by linearity (`adjoint_aeval_apply_of_forall_pow`);
2. `‖p(T)‖ ≤ ‖V†‖ ‖p(U)‖ ‖V‖ ≤ ‖p(U)‖` since `‖V†‖ = ‖V‖ ≤ 1`
   (`norm_aeval_le_norm_aeval_of_dilation`);
3. for unitary `U` the element `p(U)` is normal, so `‖p(U)‖` equals its spectral radius; the
   spectral mapping theorem and `σ(U) ⊆ 𝕊¹ ⊆ closedBall 0 1` bound this by the sup-norm of `p` on
   the closed unit disk (`norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary`).

## Main declarations

* `norm_eval_le_polynomialSupNorm` — `‖p.eval z‖ ≤ polynomialSupNorm p X` for `z ∈ X` whenever
  the values of `p` on `X` are bounded; `polynomialSupNorm_nonneg`; and
  `bddAbove_norm_eval_image_of_isCompact` for compact `X`.
* `norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary` — step 3, in any C*-algebra.
* `adjoint_aeval_apply_of_forall_pow`, `norm_aeval_le_norm_aeval_of_dilation` — steps 1–2.
* `vonNeumann_inequality_of_exists_unitary_power_dilation` — the inequality for any `T`
  admitting a unitary power dilation (the exact conclusion of L3.1 as a hypothesis).
* `vonNeumann_inequality` — the boundary theorem for contractions, obtained by applying the
  preceding dilation inequality to L3.1 (`exists_unitary_power_dilation`).

Requires `[CompleteSpace E]` (adjoints, the C*-algebra structure on `E →L[ℂ] E`).
-/
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Dilation.Schaeffer
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.SpectralSet.Basic
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
/-! ### The polynomial sup-norm -/
/-- The polynomial sup-norm is nonnegative. -/
theorem polynomialSupNorm_nonneg (p : ℂ[X]) (X : Set ℂ) : 0 ≤ polynomialSupNorm p X :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
/-- If the values `‖p.eval z‖`, `z ∈ X`, are bounded above, then each of them is at most
`polynomialSupNorm p X`. -/
theorem norm_eval_le_polynomialSupNorm (p : ℂ[X]) {X : Set ℂ}
    (hX : BddAbove ((fun z => ‖p.eval z‖) '' X)) {z : ℂ} (hz : z ∈ X) :
    ‖p.eval z‖ ≤ polynomialSupNorm p X := by
  obtain ⟨M, hM⟩ := hX
  unfold polynomialSupNorm
  refine le_ciSup₂ (f := fun z (_ : z ∈ X) => ‖p.eval z‖) ⟨M, ?_⟩ z hz
  rintro y hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨w, hw⟩ := hy
  rw [Set.mem_range] at hw
  obtain ⟨hwX, rfl⟩ := hw
  exact hM ⟨w, hwX, rfl⟩
/-- On a compact set the values `‖p.eval z‖` are bounded above. -/
theorem bddAbove_norm_eval_image_of_isCompact (p : ℂ[X]) {K : Set ℂ} (hK : IsCompact K) :
    BddAbove ((fun z => ‖p.eval z‖) '' K) :=
  hK.bddAbove_image p.continuous.norm.continuousOn
/-! ### Polynomials in a unitary -/
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

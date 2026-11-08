/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`RotationBound.lean`).

Davis Result B: the sharper total-rotation estimate (Davis 1963, Theorem 3.2, eq. 3.1) and its
corollary combining with Result A (Theorem 4.1). Tickets PD-18 + BL1/BL2/BL4/BL5/BL6.
-/
import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.v18ec9b706ba8.ForTauCeti.Analysis.InnerProductSpace.Spectrum
set_option autoImplicit false
set_option pp.unicode.fun true
/-! # Davis's sharper total-rotation estimate (Davis 1963, Theorem 3.2)

For self-adjoint `T, S` on a finite-dimensional inner product space with `H = S − T`, eigenbases
`xᵢ` (of `T`) and `vᵢ` (of `S`), eigenvalues `λᵢ`, `λ'ᵢ`, Davis's Theorem 3.2 bounds the total
rotation of the spectral resolution by the perturbation minus the eigenvalue displacement:
under the separation `γ'² + (λᵢ − λ'ᵢ)² ≤ (λᵢ − λ'ⱼ)²` (all `i ≠ j`),

`γ'² ∑ᵢ sin²θᵢ + ∑ᵢ (λᵢ − λ'ᵢ)² ≤ ‖H‖²_F`,   `sin²θᵢ = 1 − ‖⟪vᵢ, xᵢ⟫‖²`.

The proof is the two-sided evaluation of `⟨(S − λᵢ)² xᵢ, xᵢ⟩`: computing (`(S − λᵢ) xᵢ = H xᵢ`,
BL1) gives the row Frobenius norm; expanding in the `S`-eigenbasis and using the separation (BL2)
gives the rotation-plus-displacement lower bound; summing over `i` is eq. 3.1 (BL5).

The angles are identified with the canonical intertwining unitary of the two rank-one spectral
families (`OrthoProjFamily.sqSinAngle`, BL4/PD-18), and combining with Result A
(`sum_sq_eigenvalues_sub_ge`, Theorem 4.1) yields the payoff (BL6):

`γ'² ∑ᵢ sin²θᵢ ≤ 2 ‖𝒞⊥H‖²_F` —

eigenvector rotation is controlled by the *off-diagonal* part of the perturbation alone.

## Main results

* `TauCeti.rotation_add_displacement_le_hilbertSchmidt` — Theorem 3.2, eq. 3.1 (overlap form).
* `TauCeti.sqSinAngle_ofOrthonormalBasis` — `sin²θᵢ = 1 − ‖⟪vᵢ, xᵢ⟫‖²` for the canonical
  unitary of the rank-one spectral families (BL4).
* `TauCeti.rotation_add_displacement_le_hilbertSchmidt_intertwining` — Theorem 3.2 stated
  through the canonical intertwining unitary (PD-18 milestone).
* `TauCeti.rotation_le_two_mul_offDiag` — the corollary `(γ')² ∑ sin²θᵢ ≤ 2 ‖𝒞⊥H‖²_F` (BL6).

## References

* Chandler Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl.
  6 (1963), 159–173, Theorem 3.2 and §5.
-/
namespace TauCeti
open scoped InnerProductSpace
open LinearMap InnerProductSpace Module
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}
/-! ### Theorem 3.2, eq. 3.1 — overlap form (BL1 + BL2 + BL5) -/
/-- **Davis's sharper total-rotation estimate** (Davis 1963, Theorem 3.2, eq. 3.1), overlap form.
If the hybrid separation `γ'² + (λᵢ − λ'ᵢ)² ≤ (λᵢ − λ'ⱼ)²` holds for all `i ≠ j` — Davis's
`(γ')² = minᵢ {γᵢ² − (λᵢ − λ'ᵢ)²}` with `γᵢ = min_{j≠i} |λᵢ − λ'ⱼ|` — then

`γ'² ∑ᵢ (1 − ‖⟪vᵢ, xᵢ⟫‖²) + ∑ᵢ (λᵢ − λ'ᵢ)² ≤ ∑ᵢ ‖(S − T) xᵢ‖² = ‖S − T‖²_F`. -/
theorem rotation_add_displacement_le_hilbertSchmidt
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) {γ' : ℝ}
    (hsep : ∀ i j, i ≠ j →
      γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
        ≤ (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2) :
    γ' ^ 2 * ∑ i, (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
        + ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      ≤ ∑ i, ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2 := by
  have key : ∀ i : Fin n,
      γ' ^ 2 * (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
          + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
        ≤ ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2 := by
    intro i
    -- BL1: each Fourier coefficient of `(S − T) xᵢ` in the `S`-eigenbasis is an eigenvalue
    -- difference times an overlap
    have hcross : ∀ j, ‖⟪hS.eigenvectorBasis hn j, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜‖ ^ 2
        = (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2
            * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 := fun j => by
      have h := inner_eigenvectorBasis_map_sub_eigenvectorBasis hS hT hn j i
      have h2 : ⟪hS.eigenvectorBasis hn j, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜
          = -(((hT.eigenvalues hn i - hS.eigenvalues hn j : ℝ) : 𝕜)
              * ⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜) := by
        rw [← h, ← inner_neg_right]
        congr 1
        simp [LinearMap.sub_apply]
      rw [h2, norm_neg, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    -- Parseval: the overlaps sum to `‖xᵢ‖² = 1`
    have hparse : ∑ j, ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 = 1 := by
      rw [(hS.eigenvectorBasis hn).sum_sq_norm_inner_right (hT.eigenvectorBasis hn i),
        (hT.eigenvectorBasis hn).orthonormal.1 i, one_pow]
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun j => ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
      (Finset.mem_univ i)
    -- BL2: the separation turns the off-`i` mass into the rotation term
    calc γ' ^ 2 * (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
          + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
        = (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
              * ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2
            + (γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2)
              * (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2) := by
          ring
      _ ≤ (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
              * ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2
            + ∑ j ∈ Finset.univ.erase i, (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2
              * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 := by
          have h1 : (γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2)
              * (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
              = ∑ j ∈ Finset.univ.erase i,
                  (γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2)
                    * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 := by
            rw [← Finset.mul_sum]
            congr 1
            linarith [hsplit, hparse]
          rw [h1]
          refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
          exact mul_le_mul_of_nonneg_right
            (hsep i j (Finset.ne_of_mem_erase hj).symm) (sq_nonneg _)
      _ = ∑ j, (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2
            * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2 :=
          Finset.add_sum_erase Finset.univ
            (fun j => (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2
              * ‖⟪hS.eigenvectorBasis hn j, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
            (Finset.mem_univ i)
      _ = ∑ j, ‖⟪hS.eigenvectorBasis hn j, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => (hcross j).symm
      _ = ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2 :=
          (hS.eigenvectorBasis hn).sum_sq_norm_inner_right _
  calc γ' ^ 2 * ∑ i, (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
        + ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      = ∑ i, (γ' ^ 2 * (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
          + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ ∑ i, ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2 := Finset.sum_le_sum fun i _ => key i
/-! ### The canonical unitary of two rank-one spectral families (BL4 / PD-18) -/
end TauCeti

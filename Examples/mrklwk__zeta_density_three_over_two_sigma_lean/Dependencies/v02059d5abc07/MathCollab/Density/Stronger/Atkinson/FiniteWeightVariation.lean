module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_WEIGHT_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import Mathlib
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Tactic
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
structure FiniteVariationBound (f : ℕ → ℂ) (N : ℕ) (M : ℝ) : Prop where
  nonneg : 0 ≤ M
  norm_le : ∀ i : ℕ, i ≤ N → ‖f i‖ ≤ M
  variation_le : (∑ i ∈ Finset.range N, ‖f (i+1)-f i‖) ≤ M
theorem FiniteVariationBound.mono {f : ℕ → ℂ} {N : ℕ} {M D : ℝ}
    (hf : FiniteVariationBound f N M) (hMD : M ≤ D) :
    FiniteVariationBound f N D :=
  ⟨hf.nonneg.trans hMD,fun i hi => (hf.norm_le i hi).trans hMD,hf.variation_le.trans hMD⟩
theorem FiniteVariationBound.congr {f g : ℕ → ℂ} {N : ℕ} {M : ℝ}
    (hf : FiniteVariationBound f N M) (he : ∀ i ≤ N, g i = f i) :
    FiniteVariationBound g N M := by
  refine ⟨hf.nonneg,fun i hi => ?_,?_⟩
  · rw [he i hi]
    exact hf.norm_le i hi
  · convert hf.variation_le using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i (Finset.mem_range.mp hi).le,he (i+1) (Finset.mem_range.mp hi)]
theorem FiniteVariationBound.mul {f g : ℕ → ℂ} {N : ℕ} {M D : ℝ}
    (hf : FiniteVariationBound f N M) (hg : FiniteVariationBound g N D) :
    FiniteVariationBound (fun i => f i*g i) N (2*M*D) := by
  have hMD : 0 ≤ M*D := mul_nonneg hf.nonneg hg.nonneg
  refine ⟨by nlinarith,?_,?_⟩
  · intro i hi
    rw [norm_mul]
    have h := mul_le_mul (hf.norm_le i hi) (hg.norm_le i hi) (norm_nonneg _) hf.nonneg
    nlinarith
  · have hstep (i : ℕ) (hi : i ∈ Finset.range N) :
        ‖f (i+1)*g (i+1)-f i*g i‖ ≤ M*‖g (i+1)-g i‖+D*‖f (i+1)-f i‖ := by
      have hiN : i ≤ N := (Finset.mem_range.mp hi).le
      have hi1N : i+1 ≤ N := Finset.mem_range.mp hi
      rw [show f (i+1)*g (i+1)-f i*g i =
        f (i+1)*(g (i+1)-g i)+(f (i+1)-f i)*g i by ring]
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (hf.norm_le _ hi1N) (norm_nonneg _)
      · exact (mul_le_mul_of_nonneg_left (hg.norm_le _ hiN) (norm_nonneg _)).trans_eq (mul_comm _ _)
    apply (Finset.sum_le_sum hstep).trans
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    have h₁ := mul_le_mul_of_nonneg_left hg.variation_le hf.nonneg
    have h₂ := mul_le_mul_of_nonneg_left hf.variation_le hg.nonneg
    nlinarith
end MathCollab.Density.Stronger.Atkinson

module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

-- ==== Examples.jasondavies__ccdn_dimension_growth.Examples.Example_22923720987384e87402_NumberFieldEuclideanLattice ====
/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
set_option autoImplicit false
set_option warningAsError true
/-! The ring-of-integers lattice in the Euclidean mixed embedding.
The real and imaginary coordinates are unweighted; the covolume is
`2^(-r₂) √|D|`. All norm comparisons below have constants depending only
on the degree. -/
@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory
open scoped NNReal
variable (K : Type*) [Field K] [NumberField K]
/-- The mixed embedding with its Euclidean, rather than supremum, norm. -/
def euclideanNumberFieldEmbedding : K →+* mixedEmbedding.euclidean.mixedSpace K where
  toFun x := (mixedEmbedding.euclidean.toMixed K).symm (mixedEmbedding K x)
  map_zero' := by simp
  map_one' := by rw [map_one]; rfl
  map_add' x y := by simp
  map_mul' x y := by
    change (mixedEmbedding.euclidean.toMixed K).symm (mixedEmbedding K (x * y)) = _
    rw [map_mul]
    rfl

open Classical in
set_option linter.unusedVariables false in
/-- The Euclidean norm is submultiplicative on embedded field elements: the norm of the embedding of
`x * y` is at most the product of the norms of the embeddings of `x` and `y`. -/
lemma euclideanNumberFieldEmbedding_norm_mul_le (x y : K) 
    (h_CCDN_euclideanNumberFieldEmbedding_norm_sq : ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x : K),
      ‖(CCDN.euclideanNumberFieldEmbedding K : K → NumberField.mixedEmbedding.euclidean.mixedSpace K)
              x‖ ^
          2 =
        ∑ w : { w : NumberField.InfinitePlace K // w.IsReal },
            ((↑w : NumberField.InfinitePlace K) : K → ℝ) x ^ 2 +
          ∑ w : { w : NumberField.InfinitePlace K // w.IsComplex },
            ((↑w : NumberField.InfinitePlace K) : K → ℝ) x ^ 2)
    (h_CCDN_infinitePlace_le_euclidean_norm : ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (w : NumberField.InfinitePlace K)
      (x : K),
      (w : K → ℝ) x ≤
        ‖(CCDN.euclideanNumberFieldEmbedding K : K → NumberField.mixedEmbedding.euclidean.mixedSpace K)
            x‖)
    :
    ‖euclideanNumberFieldEmbedding K (x * y)‖ ≤
      ‖euclideanNumberFieldEmbedding K x‖ * ‖euclideanNumberFieldEmbedding K y‖ := by
  have hp (w : InfinitePlace K) :
      (w (x * y)) ^ 2 ≤ (w x) ^ 2 * ‖euclideanNumberFieldEmbedding K y‖ ^ 2 := by
    rw [map_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (apply_nonneg w y) (norm_nonneg _)).mpr
        (h_CCDN_infinitePlace_le_euclidean_norm K w y)) (sq_nonneg _)
  have hreal := Finset.sum_le_sum (fun w (_ : w ∈
      (Finset.univ : Finset {w : InfinitePlace K // IsReal w})) ↦ hp w.val)
  have hcomplex := Finset.sum_le_sum (fun w (_ : w ∈
      (Finset.univ : Finset {w : InfinitePlace K // IsComplex w})) ↦ hp w.val)
  rw [← Finset.sum_mul] at hreal hcomplex
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, h_CCDN_euclideanNumberFieldEmbedding_norm_sq K (x * y),
    h_CCDN_euclideanNumberFieldEmbedding_norm_sq K x]
  nlinarith only [hreal, hcomplex]

end
end CCDN

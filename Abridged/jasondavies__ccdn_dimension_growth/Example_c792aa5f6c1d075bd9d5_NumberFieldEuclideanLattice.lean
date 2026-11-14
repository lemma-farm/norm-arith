module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

-- ==== Examples.jasondavies__ccdn_dimension_growth.Examples.Example_c792aa5f6c1d075bd9d5_NumberFieldEuclideanLattice ====
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
/-- If `w x ≤ B` at every infinite place `w`, then the Euclidean embedding of `x` has norm at most
`√[K : ℚ] * B`. -/
lemma euclideanNumberFieldEmbedding_norm_le {B : ℝ} (hB : 0 ≤ B)
    (x : K) (hx : ∀ w : InfinitePlace K, w x ≤ B) 
    (h_CCDN_euclideanNumberFieldEmbedding_norm_sq : ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x : K),
      ‖(CCDN.euclideanNumberFieldEmbedding K : K → NumberField.mixedEmbedding.euclidean.mixedSpace K)
              x‖ ^
          2 =
        ∑ w : { w : NumberField.InfinitePlace K // w.IsReal },
            ((↑w : NumberField.InfinitePlace K) : K → ℝ) x ^ 2 +
          ∑ w : { w : NumberField.InfinitePlace K // w.IsComplex },
            ((↑w : NumberField.InfinitePlace K) : K → ℝ) x ^ 2)
    :
    ‖euclideanNumberFieldEmbedding K x‖ ≤ Real.sqrt (Module.finrank ℚ K) * B := by
  have hreal : (∑ w : {w : InfinitePlace K // IsReal w}, (w.val x) ^ 2) ≤
      nrRealPlaces K * B ^ 2 := by
    simpa using Finset.sum_le_sum (fun (w : {w : InfinitePlace K // IsReal w})
      (_ : w ∈ Finset.univ) ↦
      (sq_le_sq₀ (apply_nonneg w.val x) hB).mpr (hx w.val))
  have hcomplex : (∑ w : {w : InfinitePlace K // IsComplex w}, (w.val x) ^ 2) ≤
      nrComplexPlaces K * B ^ 2 := by
    simpa using Finset.sum_le_sum (fun (w : {w : InfinitePlace K // IsComplex w})
      (_ : w ∈ Finset.univ) ↦
      (sq_le_sq₀ (apply_nonneg w.val x) hB).mpr (hx w.val))
  have hrank : (nrRealPlaces K : ℝ) + 2 * nrComplexPlaces K = Module.finrank ℚ K := by
    exact_mod_cast card_add_two_mul_card_eq_rank K
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hB)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), h_CCDN_euclideanNumberFieldEmbedding_norm_sq]
  nlinarith [congrArg (fun r : ℝ ↦ r * B ^ 2) hrank,
    mul_nonneg (Nat.cast_nonneg (nrComplexPlaces K) (α := ℝ)) (sq_nonneg B)]

end
end CCDN

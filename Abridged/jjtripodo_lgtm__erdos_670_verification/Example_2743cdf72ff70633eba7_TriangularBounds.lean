module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Real.Sqrt

-- ==== Examples.jjtripodo_lgtm__erdos_670_verification.Dependencies.v9cf972db33fe.Erdos488.Geometry.SeparatedDistances.FixedDimension.FiniteHardy ====
public section
@[expose] public section
open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def hardyMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.val < i.val then 1/(i.val+1 : ℕ) else 0

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end
end

-- ==== Examples.jjtripodo_lgtm__erdos_670_verification.Examples.Example_2743cdf72ff70633eba7_TriangularBounds ====
@[expose] public section
open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Literal normalized lower-triangular coarse incidence. -/
noncomputable def coarseTriangle (n : ℕ) (P : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.val < i.val then (i.val:ℝ)/P i else 0
set_option linter.unusedVariables false in
/-- The coarse triangular estimate consumes the proved Hardy inequality,
not a per-column or unproved operator premise. -/
theorem coarseTriangle_bound {n : ℕ} (P : Fin n → ℝ)
    (hP : ∀ i, 0 < P i)
    (hquad : ∀ i, (i.val:ℝ)*(i.val+1) ≤ 2*P i) (x : Fin n → ℝ) 
    (h_Erdos488_Geometry_SeparatedDistances_FixedDimension_finite_hardy_two : ∀ (n : ℕ) (x : Fin n → ℝ),
      ∑ i : Fin n, (Erdos488.Geometry.SeparatedDistances.FixedDimension.hardyMatrix n).mulVec x i ^ 2 ≤
        4 * ∑ i : Fin n, x i ^ 2)
    :
    (∑ i, (coarseTriangle n P *ᵥ x) i ^ 2) ≤ 16*∑ i, x i ^ 2 := by
  let q : Fin n → ℝ := fun i => (i.val:ℝ)*(i.val+1)/P i
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hP i).le
  have hq2 : ∀ i, q i ≤ 2 := by
    intro i
    exact (div_le_iff₀ (hP i)).2 (hquad i)
  have he : ∀ i, (coarseTriangle n P *ᵥ x) i = q i*(hardyMatrix n *ᵥ x) i := by
    intro i
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    unfold coarseTriangle hardyMatrix q
    split_ifs
    · have hz : (i.val:ℝ)+1 ≠ 0 := by positivity
      norm_num only [Nat.cast_add,Nat.cast_one]
      field_simp
    · ring
  calc
    _ = ∑ i, (q i)^2*(hardyMatrix n *ᵥ x) i^2 := by simp_rw [he,mul_pow]
    _ ≤ ∑ i, 4*(hardyMatrix n *ᵥ x) i^2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith [hq0 i,hq2 i]
    _ = 4*∑ i, (hardyMatrix n *ᵥ x) i^2 := by rw [Finset.mul_sum]
    _ ≤ 4*(4*∑ i, x i^2) := mul_le_mul_of_nonneg_left (h_Erdos488_Geometry_SeparatedDistances_FixedDimension_finite_hardy_two n x) (by norm_num)
    _ = _ := by ring

end Erdos488.Geometry.SeparatedDistances.FixedDimension

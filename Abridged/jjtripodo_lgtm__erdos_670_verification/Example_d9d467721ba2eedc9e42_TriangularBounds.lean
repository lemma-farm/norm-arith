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

-- ==== Examples.jjtripodo_lgtm__erdos_670_verification.Examples.Example_d9d467721ba2eedc9e42_TriangularBounds ====
@[expose] public section
open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
/-- Diagonal-weighted strict upper triangular fine incidence. -/
noncomputable def fineTriangle (n : ℕ) (P : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.val < j.val then 1/P i else 0
/-- A uniform denominator bound controls the entire fine matrix. -/
theorem fineTriangle_bound {n : ℕ} (P : Fin n → ℝ) {K : ℝ}
    (hK : 0 < K) (hn : (n:ℝ) ≤ K) (hP : ∀ i, K ≤ P i) (x : Fin n → ℝ) :
    (∑ i, (fineTriangle n P *ᵥ x) i ^ 2) ≤ ∑ i, x i ^ 2 := by
  have ha : ∀ i j, (fineTriangle n P i j)^2 ≤ 1/K^2 := by
    intro i j
    unfold fineTriangle
    split_ifs
    · rw [div_pow,one_pow]
      apply one_div_le_one_div_of_le (sq_pos_of_pos hK)
      nlinarith [hP i]
    · simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      positivity
  have hx : 0 ≤ ∑ j, x j^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hl : ∀ i, (fineTriangle n P *ᵥ x) i ^ 2 ≤ ((n:ℝ)/K^2)*∑ j, x j^2 := by
    intro i
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fineTriangle n P i) x
    have hs : ∑ j, (fineTriangle n P i j)^2 ≤ (n:ℝ)/K^2 := by
      calc
        _ ≤ ∑ j : Fin n, 1/K^2 := Finset.sum_le_sum fun j _ => ha i j
        _ = _ := by simp; ring
    exact hc.trans (mul_le_mul_of_nonneg_right hs hx)
  calc
    _ ≤ ∑ i : Fin n, ((n:ℝ)/K^2)*∑ j, x j^2 := Finset.sum_le_sum fun i _ => hl i
    _ = ((n:ℝ)^2/K^2)*∑ j, x j^2 := by simp; ring
    _ ≤ 1*∑ j, x j^2 := by
      apply mul_le_mul_of_nonneg_right _ hx
      apply (div_le_iff₀ (sq_pos_of_pos hK)).2
      nlinarith [sq_nonneg ((n:ℝ)-K)]
    _ = _ := one_mul _

end Erdos488.Geometry.SeparatedDistances.FixedDimension

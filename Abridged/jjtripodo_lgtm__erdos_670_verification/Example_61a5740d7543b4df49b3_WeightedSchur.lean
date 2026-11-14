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

-- ==== Examples.jjtripodo_lgtm__erdos_670_verification.Examples.Example_61a5740d7543b4df49b3_WeightedSchur ====
@[expose] public section
open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

set_option linter.unusedVariables false in
/-- Finite weighted Schur test at the Hardy constant two, stated as a
simultaneous quadratic-form bound for every input vector. -/
theorem weighted_schur_two {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (w : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, ∑ j, A i j*w j ≤ 2*w i)
    (hcol : ∀ j, ∑ i, A i j*w i ≤ 2*w j)
    (x : ι → ℝ) 
    (h_Erdos488_Geometry_SeparatedDistances_FixedDimension_nonnegative_weighted_cauchy : ∀ {ι : Type u_1} [inst : Fintype ι] (a w x : ι → ℝ),
      (∀ (i : ι), 0 ≤ a i) →
        (∀ (i : ι), 0 < w i) →
          (∑ i : ι, a i * x i) ^ 2 ≤ (∑ i : ι, a i * w i) * ∑ i : ι, a i / w i * x i ^ 2)
    :
    (∑ i, (A *ᵥ x) i ^ 2) ≤ 4*∑ j, x j ^ 2 := by
  have hlocal : ∀ i, (A *ᵥ x) i ^ 2 ≤ 2*w i * ∑ j, A i j/w j*x j^2 := by
    intro i
    have hc := h_Erdos488_Geometry_SeparatedDistances_FixedDimension_nonnegative_weighted_cauchy (A i) w x (hA i) hw
    have hz : 0 ≤ ∑ j, A i j/w j*x j^2 := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (div_nonneg (hA i j) (hw j).le) (sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_right (hrow i) hz
    simpa only [Matrix.mulVec, dotProduct] using hc.trans hh
  calc
    _ ≤ ∑ i, 2*w i * ∑ j, A i j/w j*x j^2 :=
      Finset.sum_le_sum fun i _ => hlocal i
    _ = ∑ j, (2*(∑ i, A i j*w i)/w j)*x j^2 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ j, 4*x j^2 := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply (div_le_iff₀ (hw j)).2
      linarith [hcol j]
    _ = _ := by rw [Finset.mul_sum]
end Erdos488.Geometry.SeparatedDistances.FixedDimension

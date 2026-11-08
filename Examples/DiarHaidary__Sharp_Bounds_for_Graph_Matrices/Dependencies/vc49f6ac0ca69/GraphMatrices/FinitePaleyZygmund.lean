import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vc49f6ac0ca69.GraphMatrices.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Finite probability inequalities used in the lower-bound argument. -/
namespace GraphMatrices.FiniteLaw
noncomputable section
open scoped BigOperators
variable {α : Type*} [Fintype α]
theorem expect_mul_sq_le (μ : FiniteLaw α) (f g : α → ℝ) :
    (μ.expect (fun x => f x * g x)) ^ 2 ≤
      μ.expect (fun x => f x ^ 2) * μ.expect (fun x => g x ^ 2) := by
  have hs (x : α) : Real.sqrt (μ.weight x) ^ 2 = μ.weight x :=
    Real.sq_sqrt (μ.weight_nonneg x)
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun x => Real.sqrt (μ.weight x) * f x)
    (g := fun x => Real.sqrt (μ.weight x) * g x)
  have heq (x : α) :
      (Real.sqrt (μ.weight x) * f x) * (Real.sqrt (μ.weight x) * g x) =
        μ.weight x * (f x * g x) := by
    calc
      _ = Real.sqrt (μ.weight x) ^ 2 * (f x * g x) := by ring
      _ = _ := by rw [hs x]
  have hf (x : α) :
      (Real.sqrt (μ.weight x) * f x) ^ 2 = μ.weight x * f x ^ 2 := by
    rw [mul_pow, hs x]
  have hg (x : α) :
      (Real.sqrt (μ.weight x) * g x) ^ 2 = μ.weight x * g x ^ 2 := by
    rw [mul_pow, hs x]
  simpa only [heq, hf, hg, expect] using h
end
end GraphMatrices.FiniteLaw

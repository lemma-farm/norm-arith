module
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.GibbsComparison
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.HeatBath
public import Mathlib
public import Mathlib.Data.Nat.Choose.Bounds
public section
noncomputable section
open scoped Classical Matrix Matrix.Norms.L2Operator RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
@[expose] def spinDifferenceSet {n : ℕ} (x y : Spin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ y i)
theorem spinEuclidean_distance_sq {n : ℕ} (x y : Spin n) :
    ‖spinEuclidean x - spinEuclidean y‖ ^ 2 = 4 * (hammingDist x y : ℝ) := by
  have hterm : ∀ i : Fin n, (signedSpin x i - signedSpin y i) ^ 2 =
      if x i ≠ y i then (4 : ℝ) else 0 := by
    intro i
    cases hx : x i <;> cases hy : y i <;> simp [signedSpin, hx, hy] <;> norm_num
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin n, (signedSpin x i - signedSpin y i) ^ 2) = _
  calc
    _ = ∑ i ∈ spinDifferenceSet x y, (4 : ℝ) := by
      simp only [spinDifferenceSet, Finset.sum_filter, hterm]
    _ = 4 * (hammingDist x y : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      change (hammingDist x y : ℝ) * 4 = 4 * (hammingDist x y : ℝ)
      ring
end SKConstants

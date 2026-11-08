module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0d16f1532774.PDEFoundation.Ambient.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Explicit Euclidean norm on native vectors

`PDE.Vec d = Fin d → ℝ` inherits the finite-product supremum norm. This
module supplies the distinct Euclidean dot product, squared norm, and norm
needed by energy estimates.
-/
@[expose] public section
open scoped BigOperators
namespace PDE
/-- The Euclidean dot product on native project vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i
/-- The square of the Euclidean norm on native project vectors. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x
theorem vecNormSq_eq_sum_sq {d : ℕ} (x : Vec d) :
    vecNormSq x = ∑ i, x i ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]
theorem sq_apply_le_vecNormSq {d : ℕ} (x : Vec d) (i : Fin d) :
    x i ^ 2 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j))
    (Finset.mem_univ i)
theorem vecNormSq_add_le {d : ℕ} (x y : Vec d) :
    vecNormSq (x + y) ≤
      2 * (vecNormSq x + vecNormSq y) := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq,
    vecNormSq_eq_sum_sq]
  calc
    (∑ i, (x + y) i ^ 2) ≤
        ∑ i, 2 * (x i ^ 2 + y i ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (x i - y i)]
    _ = 2 * ∑ i, (x i ^ 2 + y i ^ 2) := by
      rw [Finset.mul_sum]
    _ = 2 * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) := by
      rw [Finset.sum_add_distrib]
theorem vecNormSq_weighted_add_le {d : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (v w : Vec d) :
    vecNormSq (a • v + b • w) ≤
      a * vecNormSq v + b * vecNormSq w := by
  unfold vecNormSq vecDot
  calc
    ∑ i : Fin d, (a • v + b • w) i * (a • v + b • w) i
        ≤ ∑ i : Fin d,
            (a * (v i * v i) + b * (w i * w i)) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hnonneg :
          0 ≤ a * b * (v i - w i) ^ 2 :=
        mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    _ = a * (∑ i : Fin d, v i * v i) +
        b * (∑ i : Fin d, w i * w i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
end PDE

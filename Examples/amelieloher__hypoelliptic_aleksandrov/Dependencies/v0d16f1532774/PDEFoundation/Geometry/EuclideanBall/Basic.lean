module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0d16f1532774.PDEFoundation.Ambient.EuclideanNorm
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0d16f1532774.PDEFoundation.Geometry.Affine
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Pointwise
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
# Round balls on native vectors

Round balls are defined through the explicit Euclidean squared distance, not
the inherited finite-product metric. The squared-radius convention agrees
with the established homogenization API. Consequently, norm-membership and
radius-monotonicity lemmas state the required radius sign assumptions.
-/
@[expose] public section
open scoped Pointwise
namespace PDE
/-- Euclidean squared distance on native vectors. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)
/-- The explicit round Euclidean open ball. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}
theorem euclideanSqDist_weighted_add_le {d : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (x y x₀ : Vec d) :
    euclideanSqDist (a • x + b • y) x₀ ≤
      a * euclideanSqDist x x₀ +
        b * euclideanSqDist y x₀ := by
  have hsub :
      (a • x + b • y) - x₀ =
        a • (x - x₀) + b • (y - x₀) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      a * x i + b * y i - x₀ i =
          a * x i + b * y i - (a + b) * x₀ i := by
        rw [hab]
        ring
      _ = a * (x i - x₀ i) + b * (y i - x₀ i) := by
        ring
  rw [euclideanSqDist, hsub, euclideanSqDist]
  exact vecNormSq_weighted_add_le ha hb hab (x - x₀) (y - x₀)
theorem convex_euclideanBall {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    Convex ℝ (euclideanBall x₀ R) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  change euclideanSqDist (a • x + b • y) x₀ < R ^ 2
  have hconv :=
    euclideanSqDist_weighted_add_le ha hb hab x y x₀
  by_cases ha_zero : a = 0
  · have hb_one : b = 1 := by
      nlinarith
    calc
      euclideanSqDist (a • x + b • y) x₀
          ≤ a * euclideanSqDist x x₀ +
              b * euclideanSqDist y x₀ := hconv
      _ = euclideanSqDist y x₀ := by
        rw [ha_zero, hb_one]
        ring
      _ < R ^ 2 := hy
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
    have hx_strict :
        a * euclideanSqDist x x₀ < a * R ^ 2 :=
      mul_lt_mul_of_pos_left hx ha_pos
    have hy_le :
        b * euclideanSqDist y x₀ ≤ b * R ^ 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hy) hb
    have hweighted :
        a * euclideanSqDist x x₀ +
            b * euclideanSqDist y x₀ <
          a * R ^ 2 + b * R ^ 2 :=
      add_lt_add_of_lt_of_le hx_strict hy_le
    have hright : a * R ^ 2 + b * R ^ 2 = R ^ 2 := by
      nlinarith
    exact hconv.trans_lt (hweighted.trans_eq hright)
end PDE

module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v41877f140755.HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v41877f140755.HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureMajorant
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Integrable bounds for the time derivative away from the Gaussian pole -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
def bellmanGaussianTimeCoefficient (s : ℝ) (q : ℝ × ℝ) : ℝ :=
  9 * q.1 ^ 2 / s ^ 4 - 6 * q.1 * q.2 / s ^ 3 + q.2 ^ 2 / s ^ 2 - 2 / s
/-- A continuous polynomial bound for the time-derivative coefficient. -/
def bellmanGaussianTimeWeight (q : ℝ × ℝ) : ℝ :=
  9 * q.1 ^ 2 + 6 * |q.1 * q.2| + q.2 ^ 2 + 2
theorem bellmanGaussianTimeCoefficient_small (t : BellmanPositiveTime)
    (ht : t.val ≤ 1) (q : ℝ × ℝ) :
    |bellmanGaussianTimeCoefficient t.val q| ≤
      bellmanGaussianTimeWeight q / t.val ^ 4 := by
  have ht2 : t.val ^ 2 ≤ 1 := by nlinarith only [t.property, ht]
  have ht3 : t.val ^ 3 ≤ 1 := by
    calc t.val ^ 3 = t.val ^ 2 * t.val := by ring
         _ ≤ 1 * 1 := mul_le_mul ht2 ht t.property.le (by norm_num)
         _ = 1 := one_mul _
  have he : bellmanGaussianTimeCoefficient t.val q * t.val ^ 4 =
      9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2 - 2 * t.val ^ 3 := by
    dsimp [bellmanGaussianTimeCoefficient]
    field_simp [ne_of_gt t.property]
  apply (le_div_iff₀ (pow_pos t.property 4)).mpr
  rw [← abs_of_pos (pow_pos t.property 4), ← abs_mul, he]
  calc
    |9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2 - 2 * t.val ^ 3|
        ≤ |9 * q.1 ^ 2| + |6 * q.1 * q.2 * t.val| +
          |q.2 ^ 2 * t.val ^ 2| + |2 * t.val ^ 3| := by
            have h1 := abs_sub (9 * q.1 ^ 2) (6 * q.1 * q.2 * t.val)
            have h2 := abs_add_le (9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val)
              (q.2 ^ 2 * t.val ^ 2)
            have h3 := abs_sub
              (9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2)
              (2 * t.val ^ 3)
            linarith only [h1, h2, h3]
    _ ≤ bellmanGaussianTimeWeight q := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg q.1),
        abs_of_nonneg (sq_nonneg q.2), abs_of_pos t.property,
        abs_of_nonneg (pow_nonneg t.property.le 2),
        abs_of_nonneg (pow_nonneg t.property.le 3)]
      norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hx : |q.1| * |q.2| = |q.1 * q.2| := (abs_mul _ _).symm
      dsimp [bellmanGaussianTimeWeight]
      rw [mul_assoc 6, hx]
      nlinarith only [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 6 * |q.1 * q.2|),
        mul_le_mul_of_nonneg_left ht2 (sq_nonneg q.2), ht3]
end HypoellipticAleksandrov.KineticAleksandrov

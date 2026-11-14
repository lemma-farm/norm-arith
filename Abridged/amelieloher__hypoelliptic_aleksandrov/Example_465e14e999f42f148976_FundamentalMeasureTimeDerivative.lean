module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6f38647c1638.HypoellipticAleksandrov.KineticAleksandrov.Bellman.GaussianKernel ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Explicit positive-time Kolmogorov Gaussian

The covariance is ((2t³/3,t²),(t²,2t)). The sign of the mixed term corresponds to
forward transport with velocity v, hence the adjoint operator -v∂X+∂vv.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
/-- The Gaussian is defined only at strictly positive times. -/
abbrev BellmanPositiveTime := {t : ℝ // 0 < t}
end HypoellipticAleksandrov.KineticAleksandrov

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_465e14e999f42f148976_FundamentalMeasureTimeDerivative ====
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
theorem bellmanGaussianTimeCoefficient_large (t : BellmanPositiveTime)
    (ht : 1 ≤ t.val) (q : ℝ × ℝ) :
    |bellmanGaussianTimeCoefficient t.val q| ≤ bellmanGaussianTimeWeight q := by
  have hp (n : ℕ) : 1 ≤ t.val ^ n := one_le_pow₀ ht
  unfold bellmanGaussianTimeCoefficient
  calc
    |9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3 +
        q.2 ^ 2 / t.val ^ 2 - 2 / t.val|
        ≤ |9 * q.1 ^ 2 / t.val ^ 4| + |6 * q.1 * q.2 / t.val ^ 3| +
          |q.2 ^ 2 / t.val ^ 2| + |2 / t.val| := by
            have h1 := abs_sub (9 * q.1 ^ 2 / t.val ^ 4)
              (6 * q.1 * q.2 / t.val ^ 3)
            have h2 := abs_add_le
              (9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3)
              (q.2 ^ 2 / t.val ^ 2)
            have h3 := abs_sub
              (9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3 +
                q.2 ^ 2 / t.val ^ 2) (2 / t.val)
            linarith only [h1, h2, h3]
    _ ≤ bellmanGaussianTimeWeight q := by
      simp only [abs_div, abs_mul, abs_of_nonneg (sq_nonneg q.1),
        abs_of_nonneg (sq_nonneg q.2), abs_of_pos t.property,
        abs_of_nonneg (pow_nonneg t.property.le 2),
        abs_of_nonneg (pow_nonneg t.property.le 3),
        abs_of_nonneg (pow_nonneg t.property.le 4)]
      norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp [bellmanGaussianTimeWeight]
      rw [mul_assoc 6, ← abs_mul]
      exact add_le_add (add_le_add (add_le_add
        (div_le_self (by positivity) (hp 4))
        (div_le_self (by positivity) (hp 3)))
        (div_le_self (sq_nonneg _) (hp 2))) (div_le_self (by norm_num) ht)
end HypoellipticAleksandrov.KineticAleksandrov

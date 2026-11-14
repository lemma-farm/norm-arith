module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Order.ProjIcc

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Examples.Example_2415acbfb25473e95291_DiracState ====
set_option autoImplicit false
@[expose] public section
/-!
# Pathwise state equation for a Dirac Parisi measure

For a continuous noise path `W`, subtracting the additive term `β W` from the
post-interface state reduces the equation to an ordinary differential equation.
The bounded globally Lipschitz tanh drift gives existence on the full finite
time interval and pathwise uniqueness, using Picard–Lindelöf.
-/
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal Topology
namespace Paper
/-- The pathwise drift after the additive noise is subtracted. -/
def diracNoiseDrift (β : ℝ) (W : ℝ → ℝ) (t y : ℝ) : ℝ :=
  β ^ 2 * Real.tanh (y + β * W t)

namespace IsDiracNoiseSolution
variable {β h q : ℝ} {W Y Z : ℝ → ℝ}
end IsDiracNoiseSolution

set_option linter.unusedVariables false in
/-- The pathwise drift depends Lipschitz-continuously on the noise value. -/
theorem dist_diracNoiseDrift_noise_le (β : ℝ) (W V : ℝ → ℝ) (t y : ℝ) 
    (h_Paper_lipschitzWith_tanh : LipschitzWith 1 Real.tanh)
    :
    dist (diracNoiseDrift β W t y) (diracNoiseDrift β V t y) ≤
      β ^ 2 * |β| * dist (W t) (V t) := by
  have ht := h_Paper_lipschitzWith_tanh.dist_le_mul (y + β * W t) (y + β * V t)
  norm_num only [NNReal.coe_one, one_mul] at ht
  rw [diracNoiseDrift, diracNoiseDrift, dist_eq_norm, ← mul_sub,
    norm_mul, Real.norm_of_nonneg (sq_nonneg β)]
  calc
    β ^ 2 * ‖Real.tanh (y + β * W t) - Real.tanh (y + β * V t)‖ ≤
        β ^ 2 * dist (y + β * W t) (y + β * V t) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg β)
    _ = β ^ 2 * |β| * dist (W t) (V t) := by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, Real.norm_eq_abs]
      rw [dist_eq_norm]
      ring
end Paper

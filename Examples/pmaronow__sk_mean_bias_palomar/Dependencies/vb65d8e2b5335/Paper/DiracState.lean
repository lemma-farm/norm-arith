module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vb65d8e2b5335.Paper.Hyperbolic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Tactic
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
theorem lipschitzWith_diracNoiseDrift (β : ℝ) (W : ℝ → ℝ) (t : ℝ) :
    LipschitzWith ⟨β ^ 2, sq_nonneg β⟩ (diracNoiseDrift β W t) := by
  have hd (y : ℝ) : HasDerivAt (diracNoiseDrift β W t)
      (β ^ 2 * sech (y + β * W t) ^ 2) y :=
    ((hasDerivAt_tanh (y + β * W t)).comp_add_const y (β * W t)).const_mul (β ^ 2)
  apply lipschitzWith_of_nnnorm_deriv_le (fun y => (hd y).differentiableAt)
  intro y
  rw [(hd y).deriv]
  change ‖β ^ 2 * sech (y + β * W t) ^ 2‖ ≤ β ^ 2
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg β),
    Real.norm_of_nonneg (sq_nonneg (sech (y + β * W t)))]
  exact mul_le_of_le_one_right (sq_nonneg β) (sech_sq_le_one _)
structure IsDiracNoiseSolution (β h q : ℝ) (W Y : ℝ → ℝ) : Prop where
  initial : Y q = h
  hasDerivWithinAt : ∀ t ∈ Icc q (1 : ℝ),
    HasDerivWithinAt Y (diracNoiseDrift β W t (Y t)) (Icc q (1 : ℝ)) t
namespace IsDiracNoiseSolution
variable {β h q : ℝ} {W Y Z : ℝ → ℝ}
end IsDiracNoiseSolution
theorem lipschitzWith_tanh : LipschitzWith 1 Real.tanh := by
  have hc : (⟨(1 : ℝ) ^ 2, sq_nonneg (1 : ℝ)⟩ : ℝ≥0) = 1 :=
    Subtype.ext (by norm_num)
  have hl := lipschitzWith_diracNoiseDrift 1 (fun _ => 0) 0
  rw [hc] at hl
  have he : diracNoiseDrift 1 (fun _ => 0) 0 = Real.tanh := by
    funext y
    simp [diracNoiseDrift]
  rwa [he] at hl
/-- The pathwise drift depends Lipschitz-continuously on the noise value. -/
theorem dist_diracNoiseDrift_noise_le (β : ℝ) (W V : ℝ → ℝ) (t y : ℝ) :
    dist (diracNoiseDrift β W t y) (diracNoiseDrift β V t y) ≤
      β ^ 2 * |β| * dist (W t) (V t) := by
  have ht := lipschitzWith_tanh.dist_le_mul (y + β * W t) (y + β * V t)
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

module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.RSFunctional
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.GaussianDifferentiation
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.GaussianHeat
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# The explicit replica-symmetric heat solution before the interface

Both spatial derivatives and the backward heat PDE are verified for the
paper's actual Gaussian formula. Identifying this explicit formula with the
weak Parisi solution still requires the separately cited uniqueness theory.
-/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper
noncomputable def rsSoftDx (β q t x : ℝ) : ℝ :=
  gaussianExpectation (fun z => Real.tanh (x + β * Real.sqrt (q - t) * z))
noncomputable def rsSoftDxx (β q t x : ℝ) : ℝ :=
  gaussianExpectation (fun z => sech (x + β * Real.sqrt (q - t) * z) ^ 2)
 theorem integrable_gaussian_tanh_affine (x a : ℝ) :
    Integrable (fun z => Real.tanh (x + a * z)) (gaussianReal 0 1) := by
  have hc : Continuous (fun z : ℝ => x + a * z) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' (gaussian_continuous_tanh.comp hc).aestronglyMeasurable
  filter_upwards [] with z
  change |Real.tanh (x + a * z)| ≤ 1
  exact (Real.abs_tanh_lt_one _).le
 theorem hasDerivAt_rsSoftDx_spatial (β q t x : ℝ) :
    HasDerivAt (rsSoftDx β q t) (rsSoftDxx β q t x) x := by
  exact hasDerivAt_gaussian_shift Real.tanh (fun y => sech y ^ 2)
    (β * Real.sqrt (q - t)) x 1 gaussian_continuous_tanh (gaussian_continuous_sech.pow 2)
    (integrable_gaussian_tanh_affine x (β * Real.sqrt (q - t))) hasDerivAt_tanh
    (fun y => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact sech_sq_le_one y)
 theorem norm_rsSoftDx_le_one (β q t x : ℝ) : ‖rsSoftDx β q t x‖ ≤ 1 := by
  have hb : ∀ᵐ z ∂gaussianReal 0 1,
      ‖Real.tanh (x + β * Real.sqrt (q - t) * z)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    exact (Real.abs_tanh_lt_one _).le
  simpa [rsSoftDx, gaussianExpectation] using
    norm_integral_le_of_norm_le_const hb
end Paper

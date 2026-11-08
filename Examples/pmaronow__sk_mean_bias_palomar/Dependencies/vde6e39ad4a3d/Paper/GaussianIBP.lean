module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Gaussian
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Gaussian integration by parts

The standard Gaussian Stein identity is derived from the derivative of its
actual probability density and whole-line integration by parts. The bounded
version discharges weighted integrability. Boundary terms are discharged by
Mathlib's whole-line theorem for integrable products; no limiting boundary
identity is assumed.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
/-- The logarithmic derivative of the standard Gaussian density is `-x`. -/
theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
      (-x * Real.exp (-(x ^ 2) / 2)) x := by
    convert ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp) using 1
    · rfl
    · dsimp
      ring
  have hp : gaussianPDFReal 0 1 =
      (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2)) := by
    funext y
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [hp]
  convert he.const_mul ((Real.sqrt (2 * Real.pi))⁻¹) using 1
  ring
/-- The first absolute Gaussian moment has an integrable density on `ℝ`. -/
theorem integrable_mul_standardGaussianPDF :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert hi using 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [show -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2) / 2 by ring]
  ring
/-- Stein's identity with its three weighted integrability obligations explicit.

This is a genuine integration-by-parts proof. No Gaussian IBP identity or
boundary-limit assumption appears among the hypotheses.
-/
theorem gaussian_stein_of_weighted_integrable (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hf : Integrable (fun x => gaussianPDFReal 0 1 x * f x))
    (hdf : Integrable (fun x => gaussianPDFReal 0 1 x * df x))
    (hxf : Integrable (fun x => gaussianPDFReal 0 1 x * (x * f x))) :
    gaussianExpectation (fun x => x * f x) = gaussianExpectation df := by
  have hi : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert hxf.neg using 1
    funext x
    dsimp
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal 0 1) (u' := df)
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardGaussianPDF x)
    hi (by
      convert hdf using 1
      funext x
      exact mul_comm _ _)
    (by
      convert hf using 1
      funext x
      exact mul_comm _ _)
  have hl : (fun x => f x * (-x * gaussianPDFReal 0 1 x)) =
      (fun x => -(gaussianPDFReal 0 1 x * (x * f x))) := by
    funext x
    ring
  have hr : (fun x => df x * gaussianPDFReal 0 1 x) =
      (fun x => gaussianPDFReal 0 1 x * df x) := by
    funext x
    ring
  rw [hl, hr, integral_neg] at h
  have hs := neg_injective h
  unfold gaussianExpectation
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simpa only [smul_eq_mul] using hs
/-- Standard Gaussian integration by parts for bounded continuously
differentiable observables with bounded derivative.

This proves all weighted integrability and boundary requirements from the
boundedness hypotheses, using Gaussian density moments.
-/
theorem gaussian_stein_of_bounded (f df : ℝ → ℝ) (M K : ℝ)
    (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hb : ∀ x, ‖f x‖ ≤ M) (hdb : ∀ x, ‖df x‖ ≤ K) :
    gaussianExpectation (fun x => x * f x) = gaussianExpectation df := by
  apply gaussian_stein_of_weighted_integrable f df hd
  · exact (integrable_gaussianPDFReal 0 1).mul_bdd hf.aestronglyMeasurable
      (.of_forall hb)
  · exact (integrable_gaussianPDFReal 0 1).mul_bdd hdf.aestronglyMeasurable
      (.of_forall hdb)
  · have hi := integrable_mul_standardGaussianPDF.mul_bdd hf.aestronglyMeasurable
      (.of_forall hb)
    convert hi using 1
    funext x
    ring
end Paper

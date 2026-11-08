-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.IntrinsicGradientRegression
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.SphericalIntrinsicHessianJet
set_option autoImplicit false
/-! # Actual full-tangent Hessian and canonical zero-gradient law

A complete tangent orthonormal basis is constructed from the actual sphere
point. Gaussian coefficient regression retains the joint value/radial/Hessian
law at the specified zero gradient. The intrinsic Hessian includes the genuine
radial identity shift.
-/
@[expose] public section
namespace SlowEquilibration.IntrinsicHessianLaw
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.WholeFieldRegression
open SlowEquilibration.IntrinsicGradientRegression SlowEquilibration.SphereHessian
open scoped RealInnerProductSpace ENNReal Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
theorem actual_scalar_cross_covariance {N P : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : EuclideanDisorder N P →L[ℝ] ℝ) (A : EuclideanDisorder N P →L[ℝ] F) (w : F) :
    cov[fun J : Disorder N P => f (euclideanDisorder J),
      fun J : Disorder N P => inner ℝ w (A (euclideanDisorder J)); disorderLaw N P] =
      f (A.adjoint w) := by
  have h := (actual_flattened_gaussian N P).covariance_fun_comp
    (f := f) (g := fun g => inner ℝ w (A g)) f.continuous.measurable.aemeasurable
    (continuous_const.inner A.continuous).measurable.aemeasurable
  rw [h]
  have hf : (f : EuclideanDisorder N P → ℝ) =
      fun g => inner ℝ (f.adjoint 1) g := by
    funext g
    rw [f.adjoint_inner_left]
    simp
  have hA : (fun g : EuclideanDisorder N P => inner ℝ w (A g)) =
      fun g => inner ℝ (A.adjoint w) g := by
    funext g
    rw [A.adjoint_inner_left]
  rw [hf, hA, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply, f.adjoint_inner_left]
  simpa using congrFun hf (A.adjoint w)
end
end SlowEquilibration.IntrinsicHessianLaw

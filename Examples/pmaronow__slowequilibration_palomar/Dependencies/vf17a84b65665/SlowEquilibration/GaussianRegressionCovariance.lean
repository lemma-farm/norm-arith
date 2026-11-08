-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianRegression
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianMatrixMomentLaw
set_option autoImplicit false
/-! Actual canonical Gaussian conditioning decreases every scalar linear
variance. The centered conditional law is constructed from the full Gaussian
coefficient residual, including singular conditional covariance. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegressionCovariance
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open GaussianRegression
open scoped RealInnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]
/-- The genuine centered conditional law of a coefficient-linear object. -/
def centeredLaw (A : E →L[ℝ] F) (B : E →L[ℝ] G) : Measure G :=
  (stdGaussian E).map (B.comp (residual A))
instance centeredLaw_probability (A : E →L[ℝ] F) (B : E →L[ℝ] G) :
    IsProbabilityMeasure (centeredLaw A B) := by unfold centeredLaw;infer_instance
instance centeredLaw_gaussian (A : E →L[ℝ] F) (B : E →L[ℝ] G) :
    IsGaussian (centeredLaw A B) :=
  ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun (B.comp (residual A))).isGaussian_map
end
end SlowEquilibration.GaussianRegressionCovariance

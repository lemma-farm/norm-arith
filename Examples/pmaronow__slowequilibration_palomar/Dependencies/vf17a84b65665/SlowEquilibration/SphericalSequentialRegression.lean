-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianOrthogonalRegression
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.ValueTangentConditioning
set_option autoImplicit false
/-! Full-field disintegration at the actual specified zero tangent gradient.
The score conditioning retains every original tensor coefficient. -/
@[expose] public section
namespace SlowEquilibration.SphericalSequentialRegression
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw SlowEquilibration.GaussianRegression
open SlowEquilibration.ValueTangentConditioning SlowEquilibration.SphericalForm
open scoped ENNReal Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def valueCLM {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    EuclideanDisorder N P →L[ℝ] ℝ := flatJetCLM c 0 x (fun i => Fin.elim0 i)
end
end SlowEquilibration.SphericalSequentialRegression

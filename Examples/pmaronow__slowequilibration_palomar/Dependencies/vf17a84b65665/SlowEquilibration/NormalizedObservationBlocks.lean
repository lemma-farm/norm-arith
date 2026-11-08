-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.CovarianceProfileOrders
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.NormalizedObservationCoercivity
set_option autoImplicit false
/-! The actual normalized score and tangent-gradient blocks, with literal
coefficient duals used in the two-point Gaussian density calculations. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open SphericalModel SphericalGaussianJet WholeFieldRegression
open scoped RealInnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
lemma gradientCLM_dual {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (v : EuclideanSpace ℝ (Fin m)) :
    (innerSL ℝ v).comp (gradientCLM c x e)=flatJetCLM c 1 x (fun _ => frameSum e v) := by
  ext g
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,PiLp.inner_apply,
    RCLike.inner_apply,conj_trivial,gradientCLM_apply,flatJetCLM_apply,jet_one_frameSum]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
end
end SlowEquilibration.NormalizedPairObservations

-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianNormMean
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianMatrixFeatures
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianCompactFeatureComparison
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.Lemmas.SpinGlass.gaussian_concentration
set_option autoImplicit false
/-! Expected spectral edge and Gaussian concentration for actual linear
Gaussian symmetric matrices under Frobenius covariance domination. -/
@[expose] public section
namespace SlowEquilibration.GaussianDominatedEdge
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK GaussianMatrixFeatures GaussianCompactMaximum
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev UnitSphere (n : ℕ) := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)
instance unitSphere_nonempty (n : ℕ) : Nonempty (UnitSphere n) := by
  refine ⟨⟨EuclideanSpace.basisFun (Fin (n+1)) ℝ 0, ?_⟩⟩
  simpa only [Metric.mem_sphere, dist_zero_right] using
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0
instance unitSphere_compact (n : ℕ) : CompactSpace (UnitSphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
end
end SlowEquilibration.GaussianDominatedEdge

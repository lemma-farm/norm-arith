-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.SphericalPairRegression
public import Mathlib.Analysis.InnerProductSpace.ProdL2
set_option autoImplicit false
/-! Actual two-point observations normalized by sqrt N on the extensive
score coordinates. Their Hilbert product carries the true L² norm. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped Topology BigOperators RealInnerProductSpace
open SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
def frameSum {N m : ℕ} (e : Fin m → Vector N) (v : EuclideanSpace ℝ (Fin m)) : Vector N :=
  ∑ i,v i • e i
lemma frameSum_norm {N m : ℕ} (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (v : EuclideanSpace ℝ (Fin m)) : ‖frameSum e v‖=‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq]
  unfold frameSum
  rw [he.inner_sum]
  simp only [conj_trivial,PiLp.inner_apply,RCLike.inner_apply]
lemma jet_one_frameSum {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (v : EuclideanSpace ℝ (Fin m)) (J : Disorder N P) :
    jet c 1 x (fun _ => frameSum e v) J=∑ i,v i*jet c 1 x (fun _ => e i) J := by
  simp only [jet,iteratedFDeriv_one_apply,frameSum,map_sum,map_smul,smul_eq_mul]
end
end SlowEquilibration.NormalizedPairObservations

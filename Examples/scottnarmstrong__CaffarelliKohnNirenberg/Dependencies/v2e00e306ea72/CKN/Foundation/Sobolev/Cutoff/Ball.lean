-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Cutoff.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Cutoff.Profile
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
/-!
# Quantitative smooth cutoffs for round balls

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent port uses the native `Fin d → ℝ` carrier and an
explicit Euclidean squared distance.

## Main definitions

* `euclideanBall` and `euclideanClosedBall`: round balls for the explicit
  Euclidean norm.
* `canonicalBallCutoff`: a smooth cutoff with a midpoint support collar.

## Main results

* `canonicalBallCutoff_smooth`, `canonicalBallCutoff_eq_one_on_inner`, and
  `canonicalBallCutoff_tsupport_subset_outer` give the qualitative cutoff
  properties.
* `canonicalBallCutoff_gradient_bound` gives the explicit bound
  `32 / (R - r)`.
-/
open Set
noncomputable section
namespace CKN
/-- Euclidean squared distance on native vectors. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)
/-- The explicit round Euclidean open ball. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}
/-- The explicit round Euclidean closed ball. -/
def euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ ≤ R ^ 2}
theorem mem_euclideanBall_iff_vecEuclideanNorm_lt {d : ℕ}
    {x₀ x : Vec d} {R : ℝ} (hR : 0 < R) :
    x ∈ euclideanBall x₀ R ↔
      vecEuclideanNorm (x - x₀) < R := by
  change vecNormSq (x - x₀) < R ^ 2 ↔
    Real.sqrt (vecNormSq (x - x₀)) < R
  exact (Real.sqrt_lt' hR).symm
theorem mem_euclideanClosedBall_iff_vecEuclideanNorm_le {d : ℕ}
    {x₀ x : Vec d} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ euclideanClosedBall x₀ R ↔
      vecEuclideanNorm (x - x₀) ≤ R := by
  change vecNormSq (x - x₀) ≤ R ^ 2 ↔
    Real.sqrt (vecNormSq (x - x₀)) ≤ R
  exact (Real.sqrt_le_left hR).symm
theorem contDiff_vecNormSq {d : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecNormSq x) := by
  unfold vecNormSq vecDot
  exact ContDiff.sum (s := Finset.univ) fun i _hi =>
    (contDiff_apply ℝ (fun _ => ℝ) i).mul (contDiff_apply ℝ (fun _ => ℝ) i)
theorem contDiff_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d => euclideanSqDist x x₀) := by
  unfold euclideanSqDist
  exact contDiff_vecNormSq.comp (contDiff_id.sub contDiff_const)
theorem isClosed_euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    IsClosed (euclideanClosedBall x₀ R) := by
  change IsClosed
    ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' Iic (R ^ 2))
  exact isClosed_Iic.preimage (contDiff_euclideanSqDist_left x₀).continuous
theorem sq_coord_sub_le_euclideanSqDist {d : ℕ}
    (x y : Vec d) (i : Fin d) :
    (x i - y i) ^ 2 ≤ euclideanSqDist x y := by
  simpa [euclideanSqDist, Pi.sub_apply] using
    sq_apply_le_vecNormSq (x - y) i
/-- A round closed ball is contained in the inherited supremum-metric closed
ball with the same nonnegative radius. -/
theorem euclideanClosedBall_subset_supClosedBall {d : ℕ}
    {x₀ : Vec d} {R : ℝ} (hR : 0 ≤ R) :
    euclideanClosedBall x₀ R ⊆ Metric.closedBall x₀ R := by
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro i
  have hsqi : (x i - x₀ i) ^ 2 ≤ R ^ 2 :=
    (sq_coord_sub_le_euclideanSqDist x x₀ i).trans hx
  have habs : |x i - x₀ i| ≤ R :=
    abs_le_of_sq_le_sq hsqi hR
  simpa [Real.dist_eq, abs_sub_comm] using habs
theorem isCompact_euclideanClosedBall {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (euclideanClosedBall x₀ R) :=
  (ProperSpace.isCompact_closedBall x₀ R).of_isClosed_subset
    (isClosed_euclideanClosedBall x₀ R)
    (euclideanClosedBall_subset_supClosedBall hR)
end CKN

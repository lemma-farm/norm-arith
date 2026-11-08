-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Statements.SuitableWeakSolutionIntegrable
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Setting.Monotonicity
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Setting.ScalingQuantities
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Topology
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
/-!
# Finiteness of the scale quantities on suitable weak solutions

The quantities `α`, `β`, `γ`, `δ`, `λ` of `paper/ckn.tex` are real-valued, so the
lemmas `lem:monotonicity` and `lem:scaling-quantities` for them carry side
conditions saying that the underlying nonnegative integrals are finite (a
necessary input when passing an `ℝ≥0∞` integral to `ℝ≥0`).  The class `def:sws`
of suitable weak solutions supplies exactly these finiteness properties on every
local box, and this file transfers them to the parabolic cylinders `Q_r(z)` of
the monotonicity and scaling statements.

The main transfer fact is that a cylinder whose closure lies in the open carrier
`Ω × I` is contained in a local box: the spatial slice is enclosed in a metric
thickening of its closed ball, and the time slice in a thickening of its closed
interval, both chosen small enough to stay inside `Ω` and `I`.
-/
/-! ### Elementary comparisons of the two norms on `Vec3` -/
/-- The Euclidean norm on `Vec3` is at most `√3` times the supremum norm. -/
private lemma vec3EuclideanNorm_le_sqrt_three_mul_norm (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    rw [show (vec3EuclideanNorm v) ^ 2 = ∑ i, v i ^ 2 by
      rw [vec3EuclideanNorm, Real.sq_sqrt]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg (v i))]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm v| ≤ |Real.sqrt 3 * ‖v‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg v),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))] at h2
end CKN

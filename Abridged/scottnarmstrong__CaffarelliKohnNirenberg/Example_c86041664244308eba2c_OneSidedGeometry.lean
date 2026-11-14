import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Snowflaking
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v320eed9e9e4c.CKN.Foundation.Parabolic.Basic ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Parabolic space-time geometry

The spatial geometry uses the Euclidean norm on `Fin 3 → ℝ`, defined from the
finite sum of squares.  This is deliberate: the ambient function space's
default norm can be the sup norm, whereas the cylinders here are Euclidean.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
abbrev Vec3 := Fin 3 → ℝ

def ParabolicPoint := Vec3 × ℝ

def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)

def vec3Ball (x : Vec3) (r : ℝ) : Set Vec3 :=
  {y | vec3EuclideanNorm (y - x) < r}
def parabolicCylinder (x : Vec3) (t r : ℝ) : Set ParabolicPoint :=
  vec3Ball x r ×ˢ Ioc (t - r ^ 2) t

end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Examples.Example_c86041664244308eba2c_OneSidedGeometry ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# One-sided cylinder covering

The truncated time shift of Step 2 in the proof of `thm:A`. For a cylinder
`𝒞_ϱ(w)` meeting the one-sided cylinder of admissible centres, and a point
`w'` of the intersection, the new centre is
`w'' = (x_{w'}, min {t_w + ϱ², 0})`: the spatial centre of `w'` and the
forward time shift truncated at the top face. It stays among the admissible
centres, and `𝒞_ϱ(w) ∩ {t ≤ 0} ⊆ 𝒞_{2ϱ}(w'')`. The covering itself needs no
upper bound on the radius.
-/
open Set
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame
/-- Shift the time coordinate forward by the squared radius, stopping at
the prescribed upper time, and use the selected point as spatial center. -/
def truncatedCylinderCenter (w w' : ParabolicPoint) (ρ T : ℝ) : ParabolicPoint :=
  (w'.1, min (w.2 + ρ ^ 2) T)
set_option linter.unusedVariables false in
theorem parabolicCylinder_inter_le_subset_truncated
    {w w' : ParabolicPoint} {ρ T : ℝ}
    (hw : w' ∈ parabolicCylinder w.1 w.2 ρ) 
    (h_CKN_Foundation_Parabolic_vec3EuclideanNorm_eq_l2 : ∀ (v : CKN.Foundation.Parabolic.Vec3),
      CKN.Foundation.Parabolic.vec3EuclideanNorm v = ‖WithLp.toLp 2 v‖)
    :
    parabolicCylinder w.1 w.2 ρ ∩ {z : ParabolicPoint | z.2 ≤ T} ⊆
      parabolicCylinder (truncatedCylinderCenter w w' ρ T).1
        (truncatedCylinderCenter w w' ρ T).2 (2 * ρ) := by
  intro z hz
  obtain ⟨hz, hzT⟩ := hz
  change vec3EuclideanNorm (z.1 - w.1) < ρ ∧
    w.2 - ρ ^ 2 < z.2 ∧ z.2 ≤ w.2 at hz
  change vec3EuclideanNorm (w'.1 - w.1) < ρ ∧
    w.2 - ρ ^ 2 < w'.2 ∧ w'.2 ≤ w.2 at hw
  change vec3EuclideanNorm (z.1 - w'.1) < 2 * ρ ∧
    min (w.2 + ρ ^ 2) T - (2 * ρ) ^ 2 < z.2 ∧
    z.2 ≤ min (w.2 + ρ ^ 2) T
  refine ⟨?_, ?_, le_min ?_ hzT⟩
  · have htriangle : vec3EuclideanNorm (z.1 - w'.1) ≤
        vec3EuclideanNorm (z.1 - w.1) + vec3EuclideanNorm (w'.1 - w.1) := by
      simp only [h_CKN_Foundation_Parabolic_vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
      simpa only [dist_eq_norm,
        norm_sub_rev (WithLp.toLp 2 w.1) (WithLp.toLp 2 w'.1)] using
        dist_triangle (WithLp.toLp 2 z.1) (WithLp.toLp 2 w.1) (WithLp.toLp 2 w'.1)
    linarith only [htriangle, hz.1, hw.1]
  · have hmin := min_le_left (w.2 + ρ ^ 2) T
    nlinarith only [hz.2.1, hmin, sq_nonneg ρ]
  · exact le_trans hz.2.2 (le_add_of_nonneg_right (sq_nonneg ρ))
end CKN.Core.Endgame

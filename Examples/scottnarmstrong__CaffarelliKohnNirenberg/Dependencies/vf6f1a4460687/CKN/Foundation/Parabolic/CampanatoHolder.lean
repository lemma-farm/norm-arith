-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Parabolic.Campanato
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Statements.ParabolicHolderVecOn
set_option autoImplicit false
set_option warningAsError true
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
private def vec3ScaleLinear (a : ℝ) : Vec3 →ₗ[ℝ] Vec3 :=
  a • LinearMap.id
private lemma vec3ScaleLinear_apply (a : ℝ) (v : Vec3) :
    vec3ScaleLinear a v = a • v := by
  rfl
private lemma vec3ScaleLinear_det (a : ℝ) :
    LinearMap.det (vec3ScaleLinear a) = a ^ 3 := by
  simp [vec3ScaleLinear, LinearMap.det_smul, LinearMap.det_id]
end CKN.Foundation.Parabolic

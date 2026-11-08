-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Setting.Finiteness
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
theorem gamma_cube_eq (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ)
    (hr : 0 < r) :
    gamma u z r ^ 3 = r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
  rw [gamma, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · positivity
end CKN

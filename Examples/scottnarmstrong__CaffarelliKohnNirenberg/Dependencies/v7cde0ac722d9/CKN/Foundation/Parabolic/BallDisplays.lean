-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
set_option autoImplicit false
set_option warningAsError true
/-!
# The parabolic ball and its volume

This file records the literal displays of `paper/ckn.tex` that describe the
open parabolic ball `𝔅_r(z)` of the metric `dpar` (equation
`eq:parabolic-ball` and Lemma `lem:parabolic-metric`):

* `𝔅_r(z) = B_r(x) × (t - r², t + r²)` for `z = (x, t)`;
* `C_r(z) ⊆ 𝔅_r(z)` and `𝔅_r(z) ⊆ C_{2r}(x, t + r²)`, where `C_r(z)` is the
  parabolic cylinder `B_r(x) × (t - r², t]`;
* `|𝔅_r(z)| = (8π/3) r⁵`.

The spatial ball `vec3Ball x r` uses the Euclidean norm on `Fin 3 → ℝ`
(`vec3EuclideanNorm`), so its volume is computed by transporting Mathlib's
volume of the Euclidean ball in `EuclideanSpace ℝ (Fin 3)` along the
measure-preserving equivalence `WithLp.toLp 2`.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
lemma volume_vec3Ball_zero (r : ℝ) :
    volume (vec3Ball (0 : Vec3) r) =
      ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [show vec3Ball (0 : Vec3) r =
      (fun y : Vec3 => WithLp.toLp 2 y) ⁻¹'
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r) from by
    ext y
    simp only [mem_vec3Ball, mem_preimage, mem_ball, dist_zero_right, sub_zero,
      vec3EuclideanNorm_eq_l2]]
  rw [(PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    measurableSet_ball.nullMeasurableSet]
  exact EuclideanSpace.volume_ball_fin_three (0 : EuclideanSpace ℝ (Fin 3)) r
/-- The volume of the open Euclidean ball of radius `r` centred at any point of
`Vec3`, namely `(4π/3) r³`; this is `volume_vec3Ball_zero` together with
translation invariance of Lebesgue measure. -/
lemma volume_vec3Ball_eq (x : Vec3) (r : ℝ) :
    volume (vec3Ball x r) =
      ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [volume_vec3Ball, volume_vec3Ball_zero]
end CKN.Foundation.Parabolic

-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.Homogenization.Geometry.TriadicPartition
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.Homogenization.Geometry.CubeMeasure
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.Homogenization.Multiscale.CubeAverage
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
open scoped BigOperators
theorem cubeAverage_const {d : ℕ} (Q : TriadicCube d) (c : ℝ) :
    cubeAverage Q (fun _ => c) = c := by
  have hvol : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  have hreal : MeasureTheory.volume.real (cubeSet Q) = cubeVolume Q := by
    simp [MeasureTheory.measureReal_def, volume_cubeSet_toReal]
  calc
    cubeAverage Q (fun _ => c)
      = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, c ∂MeasureTheory.volume := rfl
    _ = (cubeVolume Q)⁻¹ * (MeasureTheory.volume.real (cubeSet Q) * c) := by
      simp [MeasureTheory.integral_const, smul_eq_mul]
    _ = (cubeVolume Q)⁻¹ * (cubeVolume Q * c) := by rw [hreal]
    _ = ((cubeVolume Q)⁻¹ * cubeVolume Q) * c := by ring
    _ = c := by rw [inv_mul_cancel₀ hvol, one_mul]
end Homogenization

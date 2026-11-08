-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.Homogenization.Geometry.BoundaryLayer
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
theorem CubeMeasure.cubeScaleFactor_pos {d : ℕ} (Q : TriadicCube d) :
    0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
theorem cubeSet_eq_pi_Ico {d : ℕ} (Q : TriadicCube d) :
    cubeSet Q =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Ico
            ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
            ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))) := by
  ext x
  simp [cubeSet]
@[simp] theorem volume_cubeSet_toReal {d : ℕ} (Q : TriadicCube d) :
    (MeasureTheory.volume (cubeSet Q)).toReal = cubeVolume Q := by
  let a : Fin d → ℝ := fun i => ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q
  let b : Fin d → ℝ := fun i => ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    nlinarith [CubeMeasure.cubeScaleFactor_pos Q]
  rw [cubeSet_eq_pi_Ico]
  have hside : ∀ i : Fin d, b i - a i = cubeScaleFactor Q := by
    intro i
    dsimp [a, b]
    ring
  calc
    (MeasureTheory.volume
        (Set.pi Set.univ
          (fun i : Fin d =>
            Set.Ico
              ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
              ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))))).toReal
        = ∏ i : Fin d, (b i - a i) := by
          simpa [a, b] using Real.volume_pi_Ico_toReal (ι := Fin d) hab
    _ = cubeVolume Q := by
      calc
        ∏ i : Fin d, (b i - a i) = ∏ _i : Fin d, cubeScaleFactor Q := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact hside i
        _ = cubeVolume Q := by
          simp [cubeVolume]
theorem cubeVolume_pos {d : ℕ} (Q : TriadicCube d) :
    0 < cubeVolume Q := by
  have hscale : 0 < cubeScaleFactor Q := CubeMeasure.cubeScaleFactor_pos Q
  simpa [cubeVolume] using pow_pos hscale d
theorem cubeVolume_nonneg {d : ℕ} (Q : TriadicCube d) :
    0 ≤ cubeVolume Q := by
  exact le_of_lt (cubeVolume_pos Q)
end Homogenization

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

-- ==== Examples.CoolRmal__falconer_packing.Examples.Example_5cb9c642a0f492a6d6a7_SelectedTubeGeometry ====
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
set_option autoImplicit false
/-!
# Geometric containment for selected tube tests

Rectangles below are specified by their half-widths. The proof allows a change of frame
of order a/b, and keeps the transverse and longitudinal bounds separate.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open Classical
namespace FalconerPacking
/-- A closed rectangle centered at c, with half-widths a and b in the frame O. -/
def frameRectangle
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | |(O (x - c)) 0| ≤ a ∧ |(O (x - c)) 1| ≤ b}

/-- Coordinate bounds for two points in one rectangle. -/
theorem frameRectangle_sub_bounds
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c z z₀ : EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    (hz : z ∈ frameRectangle O c a b) (hz₀ : z₀ ∈ frameRectangle O c a b) :
    |(O (z - z₀)) 0| ≤ 2 * a ∧ |(O (z - z₀)) 1| ≤ 2 * b := by
  have heq : z - z₀ = (z - c) - (z₀ - c) := by abel
  change |(O (z - c)) 0| ≤ a ∧ |(O (z - c)) 1| ≤ b at hz
  change |(O (z₀ - c)) 0| ≤ a ∧ |(O (z₀ - c)) 1| ≤ b at hz₀
  rw [heq, map_sub]
  constructor
  · apply (abs_sub _ _).trans
    change |(O (z - c)) 0| + |(O (z₀ - c)) 0| ≤ 2 * a
    linarith [hz.1, hz₀.1]
  · apply (abs_sub _ _).trans
    change |(O (z - c)) 1| + |(O (z₀ - c)) 1| ≤ 2 * b
    linarith [hz.2, hz₀.2]

end FalconerPacking

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.CompleteModes
@[expose] public section
/-!
# The two link systems appearing in F₁ and F₂

After renaming vertices, each link is either the triangle, or has edges
`ab, ac, bb, cc`. The displayed solutions are linear, have operator norm
at most two in the maximum norm, and preserve zero sums across a class.
-/
namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open Finset
theorem star_loop_link_bound (x y z D : ℝ)
    (hx : |x| ≤ D) (hy : |y| ≤ D) (hz : |z| ≤ D) :
    |x| ≤ D ∧ |(0 : ℝ)| ≤ D ∧ |(y - x) / 2| ≤ D ∧ |z / 2| ≤ D := by
  have hD := (abs_nonneg x).trans hx
  rw [abs_le] at hx hy hz
  refine ⟨abs_le.mpr hx, by simpa using hD, ?_, ?_⟩ <;>
    rw [abs_le] <;> constructor <;> linarith
theorem triangle_link_bound (x y z D : ℝ)
    (hx : |x| ≤ D) (hy : |y| ≤ D) (hz : |z| ≤ D) :
    |(x + y - z) / 2| ≤ 2 * D ∧
    |(x + z - y) / 2| ≤ 2 * D ∧
    |(y + z - x) / 2| ≤ 2 * D := by
  have hD := (abs_nonneg x).trans hx
  rw [abs_le] at hx hy hz
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith
variable {V : Type*} [Fintype V]
end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

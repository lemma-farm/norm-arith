/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Inverse
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.UniversalFamilies
@[expose] public section
/-!
# Framework for the complete signed inverse of the six base families

`TernaryInverse F` is the ternary form of the bounded signed inverse (symmetric ternary weights
supported on `F`-admissible triples, with load equal to any bounded `F`-supported symmetric demand
and every weight at most `2^20 ε/(γ^6 n)`). It needs no compatibility condition: the six base
families have type vectors spanning all allowed class-pair coordinates.

`completeInverseCert_of_ternary` turns it into `CompleteInverseCert F` for every `F ⊇ F0` with the
same allowed pairs (the copy step of the F* / Fbit certificates).

`lc d a₀ a₁ a₂ a₃` is a linear combination of the four row demands of a vertex; it is used as the
input of the vertex modes.
-/
noncomputable section
namespace PaddedNoCommon
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedF12 PaddedGeneral
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A linear combination of the four row demands of a vertex. -/
def lc (d : V → Fin 4 → ℝ) (a0 a1 a2 a3 : ℝ) (v : V) : ℝ :=
  a0 * d v 0 + a1 * d v 1 + a2 * d v 2 + a3 * d v 3
theorem lc_sum_zero (p : V → Fin 4) (d : V → Fin 4 → ℝ) (hz : VertexDemandZero p d)
    (a0 a1 a2 a3 : ℝ) (i : Fin 4) :
    ∑ v ∈ classVertices p i, lc d a0 a1 a2 a3 v = 0 := by
  simp only [lc, sum_add_distrib, ← mul_sum]
  rw [hz i 0, hz i 1, hz i 2, hz i 3]
  ring
theorem lc_bound (d : V → Fin 4 → ℝ) (D : ℝ) (hd : ∀ a j, |d a j| ≤ D)
    (a0 a1 a2 a3 : ℝ) (v : V) :
    |lc d a0 a1 a2 a3 v| ≤ (|a0| + |a1| + |a2| + |a3|) * D := by
  unfold lc
  have h0 := abs_mul a0 (d v 0)
  have h1 := abs_mul a1 (d v 1)
  have h2 := abs_mul a2 (d v 2)
  have h3 := abs_mul a3 (d v 3)
  have m0 := mul_le_mul_of_nonneg_left (hd v 0) (abs_nonneg a0)
  have m1 := mul_le_mul_of_nonneg_left (hd v 1) (abs_nonneg a1)
  have m2 := mul_le_mul_of_nonneg_left (hd v 2) (abs_nonneg a2)
  have m3 := mul_le_mul_of_nonneg_left (hd v 3) (abs_nonneg a3)
  calc |a0 * d v 0 + a1 * d v 1 + a2 * d v 2 + a3 * d v 3|
      ≤ |a0 * d v 0| + |a1 * d v 1| + |a2 * d v 2| + |a3 * d v 3| := by
        have := abs_add_le (a0 * d v 0 + a1 * d v 1 + a2 * d v 2) (a3 * d v 3)
        have := abs_add_le (a0 * d v 0 + a1 * d v 1) (a2 * d v 2)
        have := abs_add_le (a0 * d v 0) (a1 * d v 1)
        linarith
    _ ≤ _ := by rw [h0, h1, h2, h3]; linarith
/-- The vertex-mode input bound used by every base family: coefficients of total size `≤ 2`. -/
theorem lc_bound_two (d : V → Fin 4 → ℝ) (D : ℝ) (hD : 0 ≤ D) (hd : ∀ a j, |d a j| ≤ D)
    (a0 a1 a2 a3 : ℝ) (ha : |a0| + |a1| + |a2| + |a3| ≤ 2) (v : V) :
    |lc d a0 a1 a2 a3 v| ≤ 2 * D :=
  (lc_bound d D hd a0 a1 a2 a3 v).trans (mul_le_mul_of_nonneg_right ha hD)
end PaddedNoCommon

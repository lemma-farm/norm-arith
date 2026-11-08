/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.Statement
public import Mathlib
set_option autoImplicit false
/-!
# Dyadic cubes in the plane

Adapted from `FalconerPacking.Dyadic` (original attribution preserved above),
`CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/Dyadic.lean
This is the geometric cube hierarchy used in the finite gauge Frostman construction.  A dyadic square of generation `n` is a product of
half-open coordinate intervals of side `2⁻ⁿ`, indexed by integers.

* `mem_dyadicCube_iff` — membership is exactly the statement that the index is the floor index,
  so the generation-`n` cubes partition the plane;
* `dyadicCube_disjoint` — distinct cubes of one generation are disjoint;
* `dyadicCube_succ_subset` — each cube is contained in its parent, whose index is `k / 2`;
* `dist_le_of_mem_dyadicCube` — a generation-`n` cube has diameter at most `√2 / 2ⁿ`;
* `measurableSet_dyadicCube` — cubes are Borel.

This is the geometric hierarchy, not `Data.Dyadic`, which is an arithmetic number type.
-/
@[expose] public section
noncomputable section
open Set
namespace FalconerThetaGauge.GaugeFrostman
/-- The dyadic square of generation `n` with integer index `k`, half-open in each coordinate. -/
def dyadicCube (n : ℕ) (k : Fin 2 → ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ i, (k i : ℝ) ≤ 2 ^ n * x i ∧ 2 ^ n * x i < (k i : ℝ) + 1}
/-- The index of the generation-`n` cube containing `x`. -/
def cubeIndex (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℤ := fun i ↦ ⌊(2 : ℝ) ^ n * x i⌋
theorem mem_dyadicCube_iff {n : ℕ} {k : Fin 2 → ℤ} {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ dyadicCube n k ↔ cubeIndex n x = k := by
  constructor
  · intro h
    funext i
    exact Int.floor_eq_iff.2 ⟨(h i).1, (h i).2⟩
  · intro h i
    have hi : ⌊(2 : ℝ) ^ n * x i⌋ = k i := congrFun h i
    rw [← hi]
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
theorem mem_dyadicCube_cubeIndex (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) : x ∈ dyadicCube n (cubeIndex n x) :=
  mem_dyadicCube_iff.2 rfl
/-- Distinct cubes of the same generation are disjoint. -/
theorem dyadicCube_disjoint {n : ℕ} {k k' : Fin 2 → ℤ} (h : k ≠ k') :
    Disjoint (dyadicCube n k) (dyadicCube n k') := by
  refine Set.disjoint_left.2 fun x hx hx' ↦ h ?_
  rw [← mem_dyadicCube_iff.1 hx, mem_dyadicCube_iff.1 hx']
/-- The index of the parent cube is the index halved. -/
theorem cubeIndex_succ (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    cubeIndex n x = fun i ↦ cubeIndex (n + 1) x i / 2 := by
  funext i
  have h : (2 : ℝ) ^ n * x i = ((2 : ℝ) ^ (n + 1) * x i) / (2 : ℕ) := by
    push_cast
    ring
  rw [cubeIndex, cubeIndex, h, Int.floor_div_natCast]
  norm_num
theorem measurableSet_dyadicCube (n : ℕ) (k : Fin 2 → ℤ) :
    MeasurableSet (dyadicCube n k) := by
  have hset : dyadicCube n k
      = ⋂ i, (fun x : EuclideanSpace ℝ (Fin 2) ↦ (2 : ℝ) ^ n * x i) ⁻¹' Ico ((k i : ℝ)) ((k i : ℝ) + 1) := by
    ext x
    simp [dyadicCube, Set.mem_Ico]
  rw [hset]
  refine MeasurableSet.iInter fun i ↦ ?_
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin 2) ↦ (2 : ℝ) ^ n * x i := by fun_prop
  exact hmeas measurableSet_Ico
section Counting
end Counting
section Ancestors
/-- The index of the generation-`n` ancestor, `m` levels up. -/
def ancestor (m : ℕ) (k : Fin 2 → ℤ) : Fin 2 → ℤ := fun i ↦ k i / 2 ^ m
@[simp] theorem ancestor_zero (k : Fin 2 → ℤ) : ancestor 0 k = k := by
  funext i
  simp [ancestor]
theorem ancestor_succ (m : ℕ) (k : Fin 2 → ℤ) :
    ancestor (m + 1) k = ancestor m (fun i ↦ k i / 2) := by
  funext i
  simp only [ancestor]
  rw [Int.ediv_ediv_of_nonneg (by norm_num : (0 : ℤ) ≤ 2), pow_succ, mul_comm]
/-- Each cube sits inside the cube of the previous generation with halved index. -/
theorem dyadicCube_subset_parent (n : ℕ) (k : Fin 2 → ℤ) :
    dyadicCube (n + 1) k ⊆ dyadicCube n (fun i ↦ k i / 2) := by
  intro y hy
  have hy' : cubeIndex (n + 1) y = k := mem_dyadicCube_iff.1 hy
  refine mem_dyadicCube_iff.2 ?_
  rw [cubeIndex_succ n y, hy']
/-- Iterating the parent map: each cube sits inside its `m`-th ancestor. -/
theorem dyadicCube_subset_ancestor (j m : ℕ) (k : Fin 2 → ℤ) :
    dyadicCube (j + m) k ⊆ dyadicCube j (ancestor m k) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
      intro y hy
      have hy' : y ∈ dyadicCube (j + m + 1) k := by
        rwa [show j + (m + 1) = j + m + 1 by ring] at hy
      have hstep := dyadicCube_subset_parent (j + m) k hy'
      have := ih (fun i ↦ k i / 2) hstep
      rwa [← ancestor_succ] at this
end Ancestors
end FalconerThetaGauge.GaugeFrostman

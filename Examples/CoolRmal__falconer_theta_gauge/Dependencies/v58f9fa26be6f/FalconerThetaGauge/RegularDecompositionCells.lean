module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.GaugeFrostmanDyadic
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.GaugeSeparatedMeasuresGeometry
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Real
set_option autoImplicit false
/-!
# Actual terminal cells and their original measure weights

The half-open unit square has precisely `4^N` generation-`N` cells. Their
original measure weights partition its mass; this connects finite bottom-up
types to the planar measure in Lemma 5.8.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Finset
open scoped Classical ENNReal
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
/-- The finite coordinate indices of the terminal cells in the unit square. -/
def unitCellIndices (N : ℕ) : Finset (Fin 2 → ℤ) :=
  Finset.univ.image (fun k : Fin 2 → Fin (2 ^ N) ↦ fun i ↦ (k i : ℤ))
theorem mem_unitCellIndices_iff (N : ℕ) (k : Fin 2 → ℤ) :
    k ∈ unitCellIndices N ↔ ∀ i, 0 ≤ k i ∧ k i < (2 : ℤ) ^ N := by
  constructor
  · intro hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    intro i
    change 0 ≤ (j i : ℤ) ∧ (j i : ℤ) < (2 : ℤ) ^ N
    exact ⟨by exact_mod_cast (Nat.zero_le (j i).val), by exact_mod_cast (j i).isLt⟩
  · intro hk
    let j : Fin 2 → Fin (2 ^ N) := fun i ↦
      ⟨(k i).toNat, by
        have h := (hk i).2
        rw [← Int.toNat_of_nonneg (hk i).1] at h
        exact_mod_cast h⟩
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hk i).1
theorem cubeIndex_mem_unitCellIndices (N : ℕ) {x : Plane} (hx : x ∈ unitSquare) :
    cubeIndex N x ∈ unitCellIndices N := by
  apply (mem_unitCellIndices_iff N _).mpr
  intro i
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg (by positivity) (hx i).1)
  · apply Int.floor_lt.mpr
    have h := mul_lt_mul_of_pos_left (hx i).2
      (show 0 < (2 : ℝ) ^ N by positivity)
    simpa only [cubeIndex, Int.cast_pow, Int.cast_ofNat, mul_one] using h
theorem dyadicCube_subset_unitSquare (N : ℕ) {k : Fin 2 → ℤ}
    (hk : k ∈ unitCellIndices N) : dyadicCube N k ⊆ unitSquare := by
  intro x hx i
  have hi := (mem_unitCellIndices_iff N k).mp hk i
  have hlo : (0 : ℝ) ≤ k i := by exact_mod_cast hi.1
  have hhi : (k i : ℝ) + 1 ≤ (2 : ℝ) ^ N := by
    exact_mod_cast (show k i + 1 ≤ (2 : ℤ) ^ N by omega)
  have hpow : 0 < (2 : ℝ) ^ N := by positivity
  constructor <;> nlinarith [(hx i).1, (hx i).2]
/-- These half-open cubes partition exactly the half-open unit square. -/
theorem biUnion_unitCellIndices (N : ℕ) :
    (⋃ k ∈ unitCellIndices N, dyadicCube N k) = unitSquare := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
    exact dyadicCube_subset_unitSquare N hk hxk
  · intro x hx
    exact mem_iUnion₂.mpr ⟨cubeIndex N x, cubeIndex_mem_unitCellIndices N hx,
      mem_dyadicCube_cubeIndex N x⟩
/-- The terminal weights are the original measure masses, with no reweighting. -/
def unitCellWeight (μ : Measure Plane) (N : ℕ) (k : Fin 2 → ℤ) : ℝ :=
  μ.real (dyadicCube N k)
theorem unitCellWeight_nonneg (μ : Measure Plane) (N : ℕ) (k : Fin 2 → ℤ) :
    0 ≤ unitCellWeight μ N k := measureReal_nonneg
def cellUnion (N : ℕ) (S : Finset (Fin 2 → ℤ)) : Set Plane :=
  ⋃ k ∈ S, dyadicCube N k
theorem measurableSet_cellUnion (N : ℕ) (S : Finset (Fin 2 → ℤ)) :
    MeasurableSet (cellUnion N S) := by
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro _
  exact measurableSet_dyadicCube N k
theorem mem_dyadicCube_ancestor_of_mem {n N : ℕ} (hn : n ≤ N) {k : Fin 2 → ℤ}
    {x : Plane} (hx : x ∈ dyadicCube N k) :
    x ∈ dyadicCube n (ancestor (N - n) k) := by
  apply dyadicCube_subset_ancestor n (N - n) k
  simpa only [Nat.add_sub_of_le hn] using hx
/-- Intersecting a carrier with a coarser cell selects precisely the original
terminal leaves having that ancestor. -/
theorem dyadicCube_inter_cellUnion {n N : ℕ} (hn : n ≤ N) (p : Fin 2 → ℤ)
    (S : Finset (Fin 2 → ℤ)) :
    dyadicCube n p ∩ cellUnion N S =
      cellUnion N (S.filter (fun k ↦ ancestor (N - n) k = p)) := by
  ext x
  constructor
  · rintro ⟨hxp, hxS⟩
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxS
    have hxa := mem_dyadicCube_ancestor_of_mem hn hxk
    have hkp : ancestor (N - n) k = p :=
      (mem_dyadicCube_iff.mp hxa).symm.trans (mem_dyadicCube_iff.mp hxp)
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hkp⟩, hxk⟩
  · intro hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
    obtain ⟨hkS, hkp⟩ := Finset.mem_filter.mp hk
    refine ⟨?_, mem_iUnion₂.mpr ⟨k, hkS, hxk⟩⟩
    rw [← hkp]
    exact mem_dyadicCube_ancestor_of_mem hn hxk
end FalconerThetaGauge

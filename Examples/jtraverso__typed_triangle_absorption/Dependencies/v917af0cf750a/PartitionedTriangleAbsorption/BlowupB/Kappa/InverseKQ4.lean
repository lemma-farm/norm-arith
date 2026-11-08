/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v917af0cf750a.PartitionedTriangleAbsorption.BlowupB.PaddedComponents.LargeInverseFrame
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v917af0cf750a.PartitionedTriangleAbsorption.BlowupB.Kappa.G3Families
@[expose] public section
/-!
# The bounded signed inverse for `KQ4` (classes of size at least 8)

Same frame as Aristotle's `InverseFMxx` (generator `gen_km.py`): totals from the types
`001` `002` `011` `012` `333`; vertex rows from repeated, singleton, tripartite and monochromatic vertex
modes (per-mode budgets `12 m D/δ²`, `24 m D/δ²` for coefficient mass `m`); zero rows from
internal, repeated and tripartite pair modes and the monochromatic zero-row mode of class `3`.
-/
noncomputable section
namespace PaddedComponents
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedFstar PaddedNoCommon PaddedGeneral
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
def realMatrixKQ4 (t00 t01 t02 t11 t12 t33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, t02, 0], ![t01, t11, t12, 0], ![t02, t12, 0, 0], ![0, 0, 0, t33]]
theorem classTotal_realMatrixKQ4 (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KQ4 g) :
    classTotal p g = realMatrixKQ4 (classTotal p g 0 0) (classTotal p g 0 1) (classTotal p g 0 2) (classTotal p g 1 1) (classTotal p g 1 2) (classTotal p g 3 3) := by
  have h03 := classTotal_zero_of_inactive p KQ4 g hs 0 3 (by unfold Link KQ4; decide)
  have h13 := classTotal_zero_of_inactive p KQ4 g hs 1 3 (by unfold Link KQ4; decide)
  have h22 := classTotal_zero_of_inactive p KQ4 g hs 2 2 (by unfold Link KQ4; decide)
  have h23 := classTotal_zero_of_inactive p KQ4 g hs 2 3 (by unfold Link KQ4; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrixKQ4, classTotal_symmetric p g hsym 1 0, classTotal_symmetric p g hsym 2 0,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 1, classTotal_symmetric p g hsym 3 2, h03, h13, h22, h23]
def typeWeightKQ4 (p : V → Fin 4) (z001 z002 z011 z012 z333 : ℝ) (a b c : V) : ℝ :=
  repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 0 2 z002 a b c +
  repeatedTypeWeight p 1 0 z011 a b c +
  tripartiteTypeWeight p 0 1 2 z012 a b c +
  monoTypeWeight p 3 z333 a b c
theorem typeWeightKQ4_symmetric (p : V → Fin 4) (z001 z002 z011 z012 z333 : ℝ) :
    TernarySymmetric (typeWeightKQ4 p z001 z002 z011 z012 z333) := by
  unfold typeWeightKQ4
  repeat' first
    | with_reducible apply TernarySymmetric.add
    | with_reducible exact monoTypeWeight_symmetric p _ _
    | with_reducible exact repeatedTypeWeight_symmetric p _ _ _
    | with_reducible exact tripartiteTypeWeight_symmetric p _ _ _ _
    | exact monoTypeWeight_symmetric p _ _
    | exact repeatedTypeWeight_symmetric p _ _ _
    | exact tripartiteTypeWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add
theorem typeWeightKQ4_supported (p : V → Fin 4) (z001 z002 z011 z012 z333 : ℝ) :
    TernarySupported p KQ4 (typeWeightKQ4 p z001 z002 z011 z012 z333) := by
  unfold typeWeightKQ4
  repeat' first
    | with_reducible apply TernarySupported.add
    | exact monoTypeWeight_supported p KQ4 _ (by unfold Link KQ4; decide) _
    | exact aabLift_supported p KQ4 _ _ (by decide) (by unfold Link KQ4; decide) _
    | exact abcLift_supported p KQ4 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KQ4; decide) _
    | apply TernarySupported.add
theorem typeWeightKQ4_totals (p : V → Fin 4) (z001 z002 z011 z012 z333 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) :
    classTotal p (ternaryLoad (typeWeightKQ4 p z001 z002 z011 z012 z333)) =
      realMatrixKQ4 (2 * z001 + 2 * z002) (2 * z001 + 2 * z011 + 1 * z012) (2 * z002 + 1 * z012) (2 * z011) (1 * z012) (6 * z333) := by
  funext i j
  unfold typeWeightKQ4
  simp only [classTotal_ternary_add]
  have hmo := fun a z => monoTypeWeight_totals p a z (hm a) (hm1 a) (hm2 a) i j
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  have hu := fun a b c z => tripartiteTypeWeight_totals p a b c z (hm a) (hm b) (hm c) i j
  simp only [hmo, ht, hu]
  fin_cases i <;> fin_cases j <;> simp [realMatrixKQ4] <;> ring
theorem typeWeightKQ4_bound (p : V → Fin 4) (z001 z002 z011 z012 z333 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz001 : |z001| ≤ 8 * E) (hz002 : |z002| ≤ 8 * E) (hz011 : |z011| ≤ 8 * E) (hz012 : |z012| ≤ 8 * E) (hz333 : |z333| ≤ 2 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |typeWeightKQ4 p z001 z002 z011 z012 z333 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := typeWeightKQ4_supported p z001 z002 z011 z012 z333
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p KQ4 a b c := by
      intro h
      rcases hdiag with hdiag | hdiag | hdiag
      · exact h.1 hdiag
      · exact h.2.1 hdiag
      · exact h.2.2.1 hdiag
    rw [hsup a b c hbad, abs_zero]
    exact hM
  have hab : a ≠ b := fun h => hdiag (Or.inl h)
  have hac : a ≠ c := fun h => hdiag (Or.inr (Or.inl h))
  have hbc : b ≠ c := fun h => hdiag (Or.inr (Or.inr h))
  have e0 := repeatedType_normalizer_bound p 0 1 z001 E δ hE hδ hz001 hm
  have e1 := repeatedType_normalizer_bound p 0 2 z002 E δ hE hδ hz002 hm
  have e2 := repeatedType_normalizer_bound p 1 0 z011 E δ hE hδ hz011 hm
  have e3 := tripartiteType_normalizer_bound p 0 1 2 z012 E δ hE hδ hz012 hm
  have e4 := mono_normalizer_bound p 3 z333 E δ hE hδ hz333 hm
  dsimp only [typeWeightKQ4, monoTypeWeight, repeatedTypeWeight, tripartiteTypeWeight,
    aabLift, abcLift, pairSymmetrize, aabBase, abcBase]
  generalize ha : p a = i
  generalize hb : p b = j
  generalize hc : p c = k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [hab, hac, hbc]
  all_goals first
    | exact e0
    | exact e1
    | exact e2
    | exact e3
    | exact e4
    | exact hM
/-- The real compatibility of `KQ4` on class totals (the charge vanishes on the totals). -/
def CompatKQ4 (p : V → Fin 4) (g : V → V → ℝ) : Prop :=
  (1 : ℝ) * classTotal p g 0 0 + (-1 : ℝ) * classTotal p g 0 1 + (-1 : ℝ) * classTotal p g 0 2 + (1 : ℝ) * classTotal p g 1 1 + (2 : ℝ) * classTotal p g 1 2 = 0
theorem exists_type_correction_KQ4 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KQ4 g)
    (hcompat : CompatKQ4 p g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p KQ4 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  unfold CompatKQ4 at hcompat
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b11 := abs_le.mp (hbound 1 1)
  have b12 := abs_le.mp (hbound 1 2)
  have b33 := abs_le.mp (hbound 3 3)
  let z001 : ℝ := (1 / 2) * classTotal p g 0 0 + (-1 / 2) * classTotal p g 0 2 + (1 / 2) * classTotal p g 1 2
  let z002 : ℝ := (1 / 2) * classTotal p g 0 2 + (-1 / 2) * classTotal p g 1 2
  let z011 : ℝ := (1 / 2) * classTotal p g 1 1
  let z012 : ℝ := 1 * classTotal p g 1 2
  let z333 : ℝ := (1 / 6) * classTotal p g 3 3
  have hz001 : |z001| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z001] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz002 : |z002| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z002] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz011 : |z011| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z011] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz012 : |z012| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z012] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz333 : |z333| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z333] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨typeWeightKQ4 p z001 z002 z011 z012 z333, typeWeightKQ4_symmetric p _ _ _ _ _,
    typeWeightKQ4_supported p _ _ _ _ _, ?_,
    typeWeightKQ4_bound p _ _ _ _ _ E δ hE hδ hz001 hz002 hz011 hz012 hz333 hm⟩
  rw [typeWeightKQ4_totals p _ _ _ _ _ hn hn1 hn2, classTotal_realMatrixKQ4 p g hsym hs]
  congr 1 <;> dsimp only [z001, z002, z011, z012, z333] <;> linarith
def vertexWeightKQ4 (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  repeatedVertexWeight p 0 1 (lc d 1 0 0 0) a b c +
  singletonVertexWeight p 1 0 (lc d (-1 / 2) (1 / 2) (-1 / 2) 0) a b c +
  tripartiteVertexWeight p 0 1 2 (lc d 0 0 1 0) a b c +
  singletonVertexWeight p 0 1 (lc d (1 / 2) (-1 / 2) (-1 / 2) 0) a b c +
  repeatedVertexWeight p 1 0 (lc d 0 1 0 0) a b c +
  tripartiteVertexWeight p 1 0 2 (lc d 0 0 1 0) a b c +
  singletonVertexWeight p 0 2 (lc d (1 / 2) (-1 / 2) 0 0) a b c +
  tripartiteVertexWeight p 2 0 1 (lc d 0 1 0 0) a b c +
  monoVertexWeight p 3 (lc d 0 0 0 1) a b c
theorem vertexWeightKQ4_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (vertexWeightKQ4 p d) := by
  unfold vertexWeightKQ4
  repeat' first
    | with_reducible apply TernarySymmetric.add
    | with_reducible exact repeatedVertexWeight_symmetric p _ _ _
    | with_reducible exact singletonVertexWeight_symmetric p _ _ _
    | with_reducible exact tripartiteVertexWeight_symmetric p _ _ _ _
    | with_reducible exact monoVertexWeight_symmetric p _ _
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | exact monoVertexWeight_symmetric p _ _
    | apply TernarySymmetric.add
theorem vertexWeightKQ4_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p KQ4 (vertexWeightKQ4 p d) := by
  unfold vertexWeightKQ4
  repeat' first
    | with_reducible apply TernarySupported.add
    | exact monoVertexWeight_supported p KQ4 _ (by unfold Link KQ4; decide) _
    | exact aabLift_supported p KQ4 _ _ (by decide) (by unfold Link KQ4; decide) _
    | exact abcLift_supported p KQ4 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link KQ4; decide) _
    | apply TernarySupported.add
theorem vertexWeightKQ4_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p KQ4 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (hm3 : ∀ i, classSize p i - 3 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (vertexWeightKQ4 p d)) a k = d a k := by
  unfold vertexWeightKQ4
  simp only [classRow_ternary_add]
  simp only [repeatedVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz 1 0 0 0 0) (hm2 0) (hm 1),
    singletonVertexWeight_rows p 1 0 _ (lc_sum_zero p d hz (-1 / 2) (1 / 2) (-1 / 2) 0 0) (hm 1) (hm1 1),
    tripartiteVertexWeight_rows p 0 1 2 _ (lc_sum_zero p d hz 0 0 1 0 0) (hm 1) (hm 2),
    singletonVertexWeight_rows p 0 1 _ (lc_sum_zero p d hz (1 / 2) (-1 / 2) (-1 / 2) 0 1) (hm 0) (hm1 0),
    repeatedVertexWeight_rows p 1 0 _ (lc_sum_zero p d hz 0 1 0 0 1) (hm2 1) (hm 0),
    tripartiteVertexWeight_rows p 1 0 2 _ (lc_sum_zero p d hz 0 0 1 0 1) (hm 0) (hm 2),
    singletonVertexWeight_rows p 0 2 _ (lc_sum_zero p d hz (1 / 2) (-1 / 2) 0 0 2) (hm 0) (hm1 0),
    tripartiteVertexWeight_rows p 2 0 1 _ (lc_sum_zero p d hz 0 1 0 0 2) (hm 0) (hm 1),
    monoVertexWeight_rows p 3 _ (lc_sum_zero p d hz 0 0 0 1 3) (hm2 3) (hm3 3)]
  have hforb := hs a k
  generalize ha : p a = i at hforb ⊢
  fin_cases i <;> fin_cases k <;> simp [lc]
  all_goals first
    | exact (hforb (by unfold Link KQ4; decide)).symm
    | ring
theorem vertexWeightKQ4_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |vertexWeightKQ4 p d a b c| ≤ 288 * D / δ ^ 2 := by
  have hf (a0 a1 a2 a3 m : ℝ) (hm0 : |a0| + |a1| + |a2| + |a3| ≤ m) (v : V) :
      |lc d a0 a1 a2 a3 v| ≤ m * D :=
    (lc_bound d D hd a0 a1 a2 a3 v).trans (mul_le_mul_of_nonneg_right hm0 hD)
  have e0 := (vertexMode_bounds p (lc d 1 0 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 1 0 0 0 1 (by norm_num)) hm a b c).1 0 1
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e0
  have e1 := (vertexMode_bounds p (lc d (-1 / 2) (1 / 2) (-1 / 2) 0) ((3 / 2) * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ (3 / 2)) hD) hδ (hf (-1 / 2) (1 / 2) (-1 / 2) 0 (3 / 2) (by norm_num)) hm a b c).2.1 1 0
  rw [show 12 * ((3 / 2) * D) / δ ^ 2 = (12 * (3 / 2)) * (D / δ ^ 2) by ring] at e1
  have e2 := (vertexMode_bounds p (lc d 0 0 1 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 1 0 1 (by norm_num)) hm a b c).2.2 0 1 2
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e2
  have e3 := (vertexMode_bounds p (lc d (1 / 2) (-1 / 2) (-1 / 2) 0) ((3 / 2) * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ (3 / 2)) hD) hδ (hf (1 / 2) (-1 / 2) (-1 / 2) 0 (3 / 2) (by norm_num)) hm a b c).2.1 0 1
  rw [show 12 * ((3 / 2) * D) / δ ^ 2 = (12 * (3 / 2)) * (D / δ ^ 2) by ring] at e3
  have e4 := (vertexMode_bounds p (lc d 0 1 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 1 0 0 1 (by norm_num)) hm a b c).1 1 0
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e4
  have e5 := (vertexMode_bounds p (lc d 0 0 1 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 1 0 1 (by norm_num)) hm a b c).2.2 1 0 2
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e5
  have e6 := (vertexMode_bounds p (lc d (1 / 2) (-1 / 2) 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf (1 / 2) (-1 / 2) 0 0 1 (by norm_num)) hm a b c).2.1 0 2
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e6
  have e7 := (vertexMode_bounds p (lc d 0 1 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 1 0 0 1 (by norm_num)) hm a b c).2.2 2 0 1
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e7
  have e8 := monoVertexWeight_bound p 3 (lc d 0 0 0 1) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 0 1 1 (by norm_num)) hm a b c
  rw [show 24 * (1 * D) / δ ^ 2 = (24 * 1) * (D / δ ^ 2) by ring] at e8
  have hM0 : 0 ≤ D / δ ^ 2 := by positivity
  unfold vertexWeightKQ4
  rw [show 288 * D / δ ^ 2 = 288 * (D / δ ^ 2) by ring]
  generalize D / δ ^ 2 = M at e0 e1 e2 e3 e4 e5 e6 e7 e8 hM0 ⊢
  rw [abs_le] at e0 e1 e2 e3 e4 e5 e6 e7 e8 ⊢
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2, e7.1, e7.2, e8.1, e8.2]
end PaddedComponents

/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.CalderonZygmundDecomposition
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Dyadic stopping intervals for the Calderón--Zygmund decomposition

This module supplies an explicit global dyadic grid and proves the quantitative
parent/child facts behind the height-one stopping rule.  In particular, a
child of a good parent has `‖f‖`-average at most two.
-/
open Filter MeasureTheory Set
open scoped ENNReal BigOperators Function Topology
namespace QuadraticCarleson
namespace CalderonZygmundDyadicStopping
set_option autoImplicit false
noncomputable section
/-- Length of a depth-`n` cell in the dyadic grid with root length `L`. -/
def dyadicLength (L : ℝ) (n : ℕ) : ℝ := L / (2 : ℝ) ^ n
/-- The half-open dyadic cell with depth `n` and integer address `q`. -/
def dyadicInterval (L : ℝ) (n : ℕ) (q : ℤ) : Set ℝ :=
  Ico ((q : ℝ) * dyadicLength L n) (((q : ℝ) + 1) * dyadicLength L n)
theorem dyadicLength_pos {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 < dyadicLength L n := by
  exact div_pos hL (by positivity)
theorem dyadicLength_eq_pow_mul {L : ℝ} {n m : ℕ} (hnm : n ≤ m) :
    dyadicLength L n = (2 : ℝ) ^ (m - n) * dyadicLength L m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold dyadicLength
  rw [Nat.add_sub_cancel_left]
  rw [pow_add]
  field_simp
/-- At different depths, a fine dyadic cell is either contained in a given
coarser cell or disjoint from it.  This is the arithmetic laminarity property
of the half-open global dyadic grid. -/
theorem dyadicInterval_subset_or_disjoint_of_le {L : ℝ} (hL : 0 < L)
    {n m : ℕ} (hnm : n ≤ m) (q r : ℤ) :
    dyadicInterval L m r ⊆ dyadicInterval L n q ∨
      Disjoint (dyadicInterval L m r) (dyadicInterval L n q) := by
  let D : ℤ := (2 : ℕ) ^ (m - n)
  have hDpos : 0 < D := by
    dsimp [D]
    exact_mod_cast (pow_pos (by decide : 0 < (2 : ℕ)) (m - n))
  have hlen := dyadicLength_eq_pow_mul (L := L) hnm
  have hcastD : (D : ℝ) = (2 : ℝ) ^ (m - n) := by
    simp [D]
  have hdm : 0 < dyadicLength L m := dyadicLength_pos hL m
  by_cases hrange : q * D ≤ r ∧ r < (q + 1) * D
  · left
    intro x hx
    simp only [dyadicInterval, mem_Ico] at hx ⊢
    have hloZ : q * D ≤ r := hrange.1
    have hhiZ : r + 1 ≤ (q + 1) * D := by omega
    have hloR : ((q * D : ℤ) : ℝ) * dyadicLength L m ≤
        (r : ℝ) * dyadicLength L m :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hloZ) hdm.le
    have hhiR : ((r + 1 : ℤ) : ℝ) * dyadicLength L m ≤
        (((q + 1) * D : ℤ) : ℝ) * dyadicLength L m :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hhiZ) hdm.le
    rw [hlen, ← hcastD]
    push_cast at hloR hhiR ⊢
    constructor <;> nlinarith
  · right
    rw [not_and_or] at hrange
    rcases hrange with hlo | hhi
    · apply Set.disjoint_left.2
      intro x hxf hxc
      simp only [dyadicInterval, mem_Ico] at hxf hxc
      have hz : r + 1 ≤ q * D := by omega
      have hzR : ((r + 1 : ℤ) : ℝ) * dyadicLength L m ≤
          ((q * D : ℤ) : ℝ) * dyadicLength L m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hdm.le
      rw [hlen, ← hcastD] at hxc
      push_cast at hzR hxc
      nlinarith
    · apply Set.disjoint_left.2
      intro x hxf hxc
      simp only [dyadicInterval, mem_Ico] at hxf hxc
      have hz : (q + 1) * D ≤ r := by omega
      have hzR : (((q + 1) * D : ℤ) : ℝ) * dyadicLength L m ≤
          (r : ℝ) * dyadicLength L m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hdm.le
      rw [hlen, ← hcastD] at hxc
      push_cast at hzR hxc
      nlinarith
/-- Any two cells in the global dyadic grid are nested or disjoint. -/
theorem dyadicInterval_laminar {L : ℝ} (hL : 0 < L)
    (n : ℕ) (q : ℤ) (m : ℕ) (r : ℤ) :
    dyadicInterval L n q ⊆ dyadicInterval L m r ∨
      dyadicInterval L m r ⊆ dyadicInterval L n q ∨
      Disjoint (dyadicInterval L n q) (dyadicInterval L m r) := by
  rcases le_total n m with hnm | hmn
  · rcases dyadicInterval_subset_or_disjoint_of_le hL hnm q r with hsub | hdis
    · exact Or.inr (Or.inl hsub)
    · exact Or.inr (Or.inr hdis.symm)
  · rcases dyadicInterval_subset_or_disjoint_of_le hL hmn r q with hsub | hdis
    · exact Or.inl hsub
    · exact Or.inr (Or.inr hdis)
/-- Distinct cells at one fixed depth are disjoint. -/
theorem dyadicInterval_disjoint_of_sameDepth {L : ℝ} (hL : 0 < L)
    (n : ℕ) {q r : ℤ} (hqr : q ≠ r) :
    Disjoint (dyadicInterval L n q) (dyadicInterval L n r) := by
  apply Set.disjoint_left.2
  intro x hxq hxr
  simp only [dyadicInterval, mem_Ico] at hxq hxr
  have hd : 0 < dyadicLength L n := dyadicLength_pos hL n
  rcases lt_or_gt_of_ne hqr with hlt | hgt
  · have hz : q + 1 ≤ r := by omega
    have hzR : ((q + 1 : ℤ) : ℝ) * dyadicLength L n ≤
        (r : ℝ) * dyadicLength L n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hd.le
    push_cast at hzR
    linarith
  · have hz : r + 1 ≤ q := by omega
    have hzR : ((r + 1 : ℤ) : ℝ) * dyadicLength L n ≤
        (q : ℝ) * dyadicLength L n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hd.le
    push_cast at hzR
    linarith
theorem dyadicInterval_nonempty {L : ℝ} (hL : 0 < L) (n : ℕ) (q : ℤ) :
    (dyadicInterval L n q).Nonempty := by
  rw [dyadicInterval, nonempty_Ico]
  have hd := dyadicLength_pos hL n
  nlinarith
/-- The data-dependent root length.  It is strictly larger than the global
`L¹` mass, so every depth-zero cell has average at most one. -/
def rootLength (f : ℝ → ℂ) : ℝ :=
  (∫ x, ‖f x‖) + 1
theorem rootLength_pos {f : ℝ → ℂ} : 0 < rootLength f := by
  have hmass : 0 ≤ ∫ x, ‖f x‖ :=
    integral_nonneg_of_ae (μ := volume)
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  unfold rootLength
  linarith
/-- The scalar `‖f‖` average on a dyadic cell. -/
def dyadicNormAverage (f : ℝ → ℂ) (L : ℝ) (n : ℕ) (q : ℤ) : ℝ :=
  ⨍ x in dyadicInterval L n q, ‖f x‖
inductive DyadicNode where
  | root (q : ℤ)
  | left (parent : DyadicNode)
  | right (parent : DyadicNode)
  deriving DecidableEq, Encodable
/-- Depth of a dyadic node. -/
def DyadicNode.depth : DyadicNode → ℕ
  | .root _ => 0
  | .left p => p.depth + 1
  | .right p => p.depth + 1
/-- Integer address of a dyadic node in the global grid at its depth. -/
def DyadicNode.index : DyadicNode → ℤ
  | .root q => q
  | .left p => 2 * p.index
  | .right p => 2 * p.index + 1
def DyadicNode.interval (L : ℝ) (p : DyadicNode) : Set ℝ :=
  dyadicInterval L p.depth p.index
/-- The scalar norm average on the interval represented by a node. -/
def DyadicNode.normAverage (f : ℝ → ℂ) (L : ℝ) (p : DyadicNode) : ℝ :=
  dyadicNormAverage f L p.depth p.index
def ancestorsGood (f : ℝ → ℂ) (L : ℝ) (p : DyadicNode) : Prop :=
  ∀ (m : ℕ) (r : ℤ), m < p.depth →
    p.interval L ⊆ dyadicInterval L m r → dyadicNormAverage f L m r ≤ 1
/-- A first-crossing stopping node: its own norm average is above one, while
every strict ancestor has average at most one. -/
def IsStoppingNode (f : ℝ → ℂ) (L : ℝ) (p : DyadicNode) : Prop :=
  ancestorsGood f L p ∧ 1 < p.normAverage f L
/-- The subtype of intrinsic stopping nodes for the data-dependent root
length.  It is countable because the dyadic forest itself is encodable. -/
def stoppingNode (f : ℝ → ℂ) :=
  {p : DyadicNode // IsStoppingNode f (rootLength f) p}
instance stoppingNode_countable (f : ℝ → ℂ) : Countable (stoppingNode f) :=
  Subtype.val_injective.countable
structure DyadicCell where
  depth : ℕ
  index : ℤ
  deriving DecidableEq, Encodable
def DyadicCell.interval (L : ℝ) (c : DyadicCell) : Set ℝ :=
  dyadicInterval L c.depth c.index
def DyadicCell.normAverage (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : ℝ :=
  dyadicNormAverage f L c.depth c.index
/-- Every strictly coarser dyadic cell containing `c` is good. -/
def cellAncestorsGood (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : Prop :=
  ∀ (m : ℕ) (r : ℤ), m < c.depth →
    c.interval L ⊆ dyadicInterval L m r → dyadicNormAverage f L m r ≤ 1
def IsStoppingCell (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : Prop :=
  cellAncestorsGood f L c ∧ 1 < c.normAverage f L
/-- The canonical countable family of first-crossing cells. -/
def stoppingCell (f : ℝ → ℂ) :=
  {c : DyadicCell // IsStoppingCell f (rootLength f) c}
instance stoppingCell_countable (f : ℝ → ℂ) : Countable (stoppingCell f) :=
  Subtype.val_injective.countable
theorem stoppingCell_pairwiseDisjoint {f : ℝ → ℂ} :
    Pairwise (Disjoint on fun c : stoppingCell f ↦
      c.1.interval (rootLength f)) := by
  intro c d hcd
  rcases dyadicInterval_laminar rootLength_pos c.1.depth c.1.index
      d.1.depth d.1.index with hsub | hsub | hdis
  · rcases lt_trichotomy c.1.depth d.1.depth with hlt | heq | hgt
    · rcases dyadicInterval_subset_or_disjoint_of_le rootLength_pos hlt.le
          c.1.index d.1.index with hrev | hdis'
      · exact False.elim ((not_lt_of_ge (d.2.1 c.1.depth c.1.index hlt hrev)) c.2.2)
      · obtain ⟨x, hx⟩ := dyadicInterval_nonempty rootLength_pos c.1.depth c.1.index
        exact False.elim (Set.disjoint_left.1 hdis' (hsub hx) hx)
    · by_cases hi : c.1.index = d.1.index
      · apply False.elim
        apply hcd
        apply Subtype.ext
        cases hc : c.1
        cases hd : d.1
        simp_all
      · change Disjoint
          (dyadicInterval (rootLength f) c.1.depth c.1.index)
          (dyadicInterval (rootLength f) d.1.depth d.1.index)
        rw [← heq]
        exact dyadicInterval_disjoint_of_sameDepth (L := rootLength f)
          rootLength_pos c.1.depth hi
    · exact False.elim ((not_lt_of_ge
        (c.2.1 d.1.depth d.1.index hgt hsub)) d.2.2)
  · rcases lt_trichotomy d.1.depth c.1.depth with hlt | heq | hgt
    · rcases dyadicInterval_subset_or_disjoint_of_le rootLength_pos hlt.le
          d.1.index c.1.index with hrev | hdis'
      · exact False.elim ((not_lt_of_ge (c.2.1 d.1.depth d.1.index hlt hrev)) d.2.2)
      · obtain ⟨x, hx⟩ := dyadicInterval_nonempty rootLength_pos d.1.depth d.1.index
        exact False.elim (Set.disjoint_left.1 hdis' (hsub hx) hx)
    · by_cases hi : c.1.index = d.1.index
      · apply False.elim
        apply hcd
        apply Subtype.ext
        cases hc : c.1
        cases hd : d.1
        simp_all
      · change Disjoint
          (dyadicInterval (rootLength f) c.1.depth c.1.index)
          (dyadicInterval (rootLength f) d.1.depth d.1.index)
        rw [heq]
        exact dyadicInterval_disjoint_of_sameDepth (L := rootLength f)
          rootLength_pos c.1.depth hi
    · exact False.elim ((not_lt_of_ge
        (d.2.1 c.1.depth c.1.index hgt hsub)) c.2.2)
  · exact hdis
def stoppingBadUnion (f : ℝ → ℂ) : Set ℝ :=
  ⋃ c : stoppingCell f, c.1.interval (rootLength f)
end
end CalderonZygmundDyadicStopping
end QuadraticCarleson

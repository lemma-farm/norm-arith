module
/-
Directed potentials restricted to positive degree, their inverse moments and overlap identities.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Support.Pairing
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {X : Type u}
noncomputable def PhiDres (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * (if rE ρt R x = 0 then 0 else phiE α (q ρt R x))
noncomputable def zMass (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' y, ρs y * (if rE ρt R y = 0 then 1 else 0)
noncomputable def failureD (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * qE ρt R x
lemma failureD_le_PhiDres_add_zMass (α : ℝ) (hα0 : 0 ≤ α)
    (ρs ρt : PMF X) (R : X → X → Prop) :
    failureD ρs ρt R ≤ PhiDres α ρs ρt R + zMass ρs ρt R := by
  rw [failureD, PhiDres, zMass, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hr : rE ρt R x = 0
  · simp only [hr, ite_true, mul_zero, zero_add, mul_one]
    calc
      ρs x * qE ρt R x = qE ρt R x * ρs x := mul_comm _ _
      _ ≤ 1 * ρs x := mul_le_mul_left qE_le_one _
      _ = ρs x := one_mul _
  · simp only [hr, ite_false]
    have hqE : qE ρt R x = ENNReal.ofReal (q ρt R x) :=
      (ENNReal.ofReal_toReal qE_ne_top).symm
    rw [hqE, mul_zero, add_zero]
    calc
      ρs x * ENNReal.ofReal (q ρt R x)
          = ENNReal.ofReal (q ρt R x) * ρs x := mul_comm _ _
      _ ≤ phiE α (q ρt R x) * ρs x :=
        mul_le_mul_left (ofReal_le_phiE hα0 q_nonneg q_le_one) _
      _ = ρs x * phiE α (q ρt R x) := mul_comm _ _
noncomputable def WresD (α : ℝ) (ρt : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  if rE ρt R x = 0 then 0 else WnnD α ρt R x
noncomputable def HresD (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, ρs x * (if ¬ R x y then WresD α ρt R x else 0)
noncomputable def KresD (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, ρs x * (if ¬ R x y then
    (if rE ρt R x = 0 then 0 else phiE α (q ρt R x)) else 0)
lemma q_lt_one_of_rE_ne_zero {ρ : PMF X} {R : X → X → Prop} {x : X}
    (h : rE ρ R x ≠ 0) : q ρ R x < 1 := by
  have hq1 : qE ρ R x ≠ 1 := by
    intro h1
    apply h
    have hr : rE ρ R x = 1 - qE ρ R x :=
      ENNReal.eq_sub_of_add_eq qE_ne_top (rE_add_qE ρ R x)
    rw [hr, h1, tsub_self]
  have hlt : qE ρ R x < 1 := lt_of_le_of_ne qE_le_one hq1
  have := (ENNReal.toReal_lt_toReal qE_ne_top ENNReal.one_ne_top).mpr hlt
  rwa [ENNReal.toReal_one] at this
lemma HresD_le {α : ℝ} (hα : 1 ≤ α) (ρs ρt : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) (y : X) :
    HresD α ρs ρt R y ≤ qE ρs R y + ENNReal.ofReal α * KresD α ρs ρt R y := by
  have hbr : ∀ x, ρs x * (if ¬ R x y then WresD α ρt R x else 0)
      ≤ (if ¬ R x y then ρs x else 0)
        + ENNReal.ofReal α * (ρs x * (if ¬ R x y then
            (if rE ρt R x = 0 then 0 else phiE α (q ρt R x)) else 0)) := by
    intro x
    by_cases h : R x y
    · simp [h]
    · simp only [ite_eq_left h]
      by_cases hres : rE ρt R x = 0
      · rw [WresD, ite_eq_left hres, mul_zero, ite_eq_left hres, mul_zero, mul_zero]
        exact zero_le
      · rw [WresD, ite_eq_right hres, ite_eq_right hres]
        calc ρs x * WnnD α ρt R x
            ≤ ρs x * (1 + ENNReal.ofReal α * phiE α (q ρt R x)) := by
              gcongr
              exact WnnD_le hα ρt R x
          _ = ρs x + ENNReal.ofReal α * (ρs x * phiE α (q ρt R x)) := by ring
  have hqe : (∑' x, if ¬ R x y then ρs x else 0) = qE ρs R y := by
    rw [← tsum_not_rel_eq_qE hsymm]
    exact tsum_congr fun x => by by_cases h : R x y <;> simp [h]
  calc HresD α ρs ρt R y
      ≤ ∑' x, ((if ¬ R x y then ρs x else 0)
          + ENNReal.ofReal α * (ρs x * (if ¬ R x y then
              (if rE ρt R x = 0 then 0 else phiE α (q ρt R x)) else 0))) :=
        ENNReal.tsum_le_tsum hbr
    _ = qE ρs R y + ENNReal.ofReal α * KresD α ρs ρt R y := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hqe, KresD]
lemma KresD_le_PhiDres (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) :
    KresD α ρs ρt R y ≤ PhiDres α ρs ρt R := by
  rw [KresD, PhiDres]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  by_cases h : R x y <;> simp [h]
section
variable {X : Type}
end
end GraphMarkovMatching

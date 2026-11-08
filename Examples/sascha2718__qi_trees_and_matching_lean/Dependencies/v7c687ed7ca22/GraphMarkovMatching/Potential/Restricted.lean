module
/-
Directed potentials restricted to positive degree, their inverse moments and overlap identities.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Support.Pairing
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {X : Type u}
noncomputable def PhiDres (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * (if rE ρt R x = 0 then 0 else phiE α (q ρt R x))
noncomputable def WresD (α : ℝ) (ρt : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  if rE ρt R x = 0 then 0 else WnnD α ρt R x
noncomputable def HresD (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, ρs x * (if ¬ R x y then WresD α ρt R x else 0)
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
lemma fubini_swap_two_gen (μ₀ μ₁ ν : PMF X) (R : X → X → Prop)
    (G₀ G₁ : X → ℝ≥0∞) :
    ∑' p : X × X, μ₀ p.1 * μ₁ p.2
        * (cOverlap ν R p.1 p.2 * (G₀ p.1 * G₁ p.2))
      = ∑' y, ν y * ((∑' x, μ₀ x * (if ¬ R x y then G₀ x else 0))
          * ∑' x, μ₁ x * (if ¬ R x y then G₁ x else 0)) := by
  have hstep : ∀ p : X × X,
      μ₀ p.1 * μ₁ p.2 * (cOverlap ν R p.1 p.2 * (G₀ p.1 * G₁ p.2))
        = ∑' y, μ₀ p.1 * μ₁ p.2 * (G₀ p.1 * G₁ p.2)
            * (if ¬ R p.1 y ∧ ¬ R p.2 y then ν y else 0) := by
    intro p; rw [cOverlap, ENNReal.tsum_mul_left]; ring
  simp_rw [hstep]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => ?_
  rw [tsum_congr fun p : X × X => show
      μ₀ p.1 * μ₁ p.2 * (G₀ p.1 * G₁ p.2)
          * (if ¬ R p.1 y ∧ ¬ R p.2 y then ν y else 0)
        = ν y * ((μ₀ p.1 * (if ¬ R p.1 y then G₀ p.1 else 0))
                 * (μ₁ p.2 * (if ¬ R p.2 y then G₁ p.2 else 0)))
      from by by_cases h1 : R p.1 y <;> by_cases h2 : R p.2 y <;>
        simp [h1, h2]; ring]
  rw [ENNReal.tsum_mul_left, tsum_prod_split
        (fun x => μ₀ x * (if ¬ R x y then G₀ x else 0))
        (fun x => μ₁ x * (if ¬ R x y then G₁ x else 0))]
lemma fubini_swap_two_res (α : ℝ) (μ₀ μ₁ νc ν₀ ν₁ : PMF X)
    (R : X → X → Prop) :
    ∑' p : X × X, μ₀ p.1 * μ₁ p.2
        * (cOverlap νc R p.1 p.2 * (WresD α ν₀ R p.1 * WresD α ν₁ R p.2))
      = ∑' y, νc y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y) :=
  fubini_swap_two_gen μ₀ μ₁ νc R (WresD α ν₀ R) (WresD α ν₁ R)
section
variable {X : Type}
lemma rE_rpow_neg_eq_WresD {α : ℝ} (ρt : PMF X) (R : X → X → Prop) (x : X)
    (h : rE ρt R x ≠ 0) : (rE ρt R x) ^ (-α) = WresD α ρt R x := by
  rw [WresD, ite_eq_right h, WnnD]
  have hq : q ρt R x < 1 := q_lt_one_of_rE_ne_zero h
  have h1 : rE ρt R x = ENNReal.ofReal (1 - q ρt R x) := by
    rw [← toReal_rE_eq ρt R x, ENNReal.ofReal_toReal rE_ne_top]
  rw [h1, ← ENNReal.ofReal_rpow_of_pos (by linarith)]
end
end GraphMarkovMatching

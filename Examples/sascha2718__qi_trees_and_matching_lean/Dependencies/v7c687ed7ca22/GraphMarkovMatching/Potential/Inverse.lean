module
/-
Inverse powers of good degrees and their elementary potential bounds.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Potential.Directed
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {X : Type u}
lemma rpow_neg_antitone {a b : ℝ≥0∞} {β : ℝ} (hβ : 0 ≤ β) (hab : a ≤ b) :
    b ^ (-β) ≤ a ^ (-β) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow hab hβ)
lemma phiE_eq_qE_mul_rpow {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (hα : 0 < α) (v : V) :
    phiE α (q μ Rv v) = qE μ Rv v * (rE μ Rv v) ^ (-α) := by
  by_cases hq : q μ Rv v < 1
  · have hr0 : (0 : ℝ) < 1 - q μ Rv v := by linarith
    have hrE : rE μ Rv v = ENNReal.ofReal (1 - q μ Rv v) := by
      have h1 := toReal_rE_add_toReal_qE μ Rv v
      rw [show (1 : ℝ) - q μ Rv v = (rE μ Rv v).toReal from by rw [q]; linarith,
        ENNReal.ofReal_toReal rE_ne_top]
    have hqE : qE μ Rv v = ENNReal.ofReal (q μ Rv v) := by
      rw [q, ENNReal.ofReal_toReal qE_ne_top]
    rw [phiE_of_lt hq, phi, hrE, hqE, ENNReal.rpow_neg,
      ENNReal.ofReal_rpow_of_pos hr0,
      ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hr0 α), div_eq_mul_inv]
  · have hq1 : q μ Rv v = 1 := le_antisymm q_le_one (not_lt.mp hq)
    have hqE1 : qE μ Rv v = 1 := by
      rw [← ENNReal.ofReal_toReal qE_ne_top, ← q, hq1, ENNReal.ofReal_one]
    have hrE0 : rE μ Rv v = 0 := by
      have h1 := rE_add_qE μ Rv v
      rw [hqE1] at h1
      calc rE μ Rv v = rE μ Rv v + 1 - 1 :=
            (ENNReal.add_sub_cancel_right ENNReal.one_ne_top).symm
        _ = 1 - 1 := by rw [h1]
        _ = 0 := tsub_self 1
    rw [hq1, phiE_one, hqE1, hrE0, one_mul,
      ENNReal.zero_rpow_of_neg (by linarith)]
noncomputable def WnnD (α : ℝ) (ν : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - q ν R x) ^ (-α))
end GraphMarkovMatching

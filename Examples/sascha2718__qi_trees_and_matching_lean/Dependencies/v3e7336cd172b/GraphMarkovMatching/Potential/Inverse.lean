module
/-
Inverse powers of good degrees and their elementary potential bounds.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Potential.Directed
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {X : Type u}
noncomputable def WnnD (α : ℝ) (ν : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - q ν R x) ^ (-α))
lemma WnnD_le {α : ℝ} (hα : 1 ≤ α) (ν : PMF X) (R : X → X → Prop) (x : X) :
    WnnD α ν R x ≤ 1 + ENNReal.ofReal α * phiE α (q ν R x) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  rw [WnnD]
  by_cases hq : q ν R x < 1
  · have hφ : 0 ≤ phi α (q ν R x) := phi_nonneg q_nonneg hq
    rw [phiE_of_lt hq]
    calc ENNReal.ofReal ((1 - q ν R x) ^ (-α))
        ≤ ENNReal.ofReal (1 + α * phi α (q ν R x)) :=
          ENNReal.ofReal_le_ofReal (rpow_neg_alpha_le hα hq)
      _ = 1 + ENNReal.ofReal α * ENNReal.ofReal (phi α (q ν R x)) := by
          rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg hα0 hφ),
              ENNReal.ofReal_mul hα0, ENNReal.ofReal_one]
  · have hq1 : q ν R x = 1 := le_antisymm q_le_one (not_lt.mp hq)
    have h0 : (1 : ℝ) - q ν R x = 0 := by rw [hq1]; ring
    rw [h0, Real.zero_rpow (ne_of_lt (by linarith : (-α : ℝ) < 0)), ENNReal.ofReal_zero]
    exact zero_le
end GraphMarkovMatching

import Mathlib
namespace GuthMaynardS2ShortGapPhase
open Real Complex Set MeasureTheory
noncomputable section
def first (t xi u : ℝ) : ℝ := t / (2 * Real.pi * u) - xi
lemma first_lower {t xi u : ℝ} (ht : |t| ≤ |xi|)
    (hu : u ∈ Icc (1/2 : ℝ) 3) : |xi| / 2 ≤ |first t xi u| := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hden : 2 ≤ 2 * Real.pi * u := by nlinarith [Real.pi_gt_three, mul_nonneg (sub_nonneg.mpr hu.1) Real.pi_pos.le]
  have hsmall : |t / (2 * Real.pi * u)| ≤ |xi| / 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi * u)]
    exact div_le_div₀ (abs_nonneg _) ht (by norm_num) hden
  have htri := abs_sub (t / (2 * Real.pi * u)) (t / (2 * Real.pi * u) - xi)
  simp only [sub_sub_cancel] at htri
  unfold first
  linarith
end
end GuthMaynardS2ShortGapPhase
namespace GuthMaynardS2ShortGapPhase
open Real Complex Set MeasureTheory
noncomputable section
end
end GuthMaynardS2ShortGapPhase

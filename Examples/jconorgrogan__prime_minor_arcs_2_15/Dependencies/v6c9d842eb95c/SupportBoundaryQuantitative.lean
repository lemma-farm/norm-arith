import Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.v6c9d842eb95c.SupportBoundaryWeld
import Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.v6c9d842eb95c.WindowArcBoundaryWeld
/-!
# Quantitative support-boundary leaf

This file turns the exact collar certificate into the pointwise logarithmic
bound needed by the MAP variance assembly, then absorbs its square over every
legal translated window.
-/
namespace SupportBoundaryQuantitative
open scoped BigOperators ArithmeticFunction
open SupportBoundaryWeld
noncomputable section
theorem translatedWindow_card_real_le
    {H h₀ : ℝ} (hH : 0 ≤ H) :
    ((PrimePairEndpoints.translatedWindow H h₀).card : ℝ) ≤ 2 * H + 1 := by
  let a : ℤ := ⌈h₀ - H⌉
  let b : ℤ := ⌊h₀ + H⌋
  change ((Finset.Icc a b).card : ℝ) ≤ 2 * H + 1
  by_cases hab : a ≤ b + 1
  · have hcardZ : ((Finset.Icc a b).card : ℤ) = b + 1 - a :=
      Int.card_Icc_of_le a b hab
    have hcardR : ((Finset.Icc a b).card : ℝ) =
        (b : ℝ) + 1 - (a : ℝ) := by exact_mod_cast hcardZ
    rw [hcardR]
    have hb : (b : ℝ) ≤ h₀ + H := Int.floor_le _
    have ha : h₀ - H ≤ (a : ℝ) := Int.le_ceil _
    linarith
  · have hba : ¬ a ≤ b := by omega
    rw [Finset.Icc_eq_empty hba]
    simp
    linarith
/-- Every shift in a legal all-center window has the manuscript's uniform
mesoscopic size bound. -/
theorem natAbs_shift_le_two_rpow
    {X H h₀ ε : ℝ}
    (hlegal : PrimePairEndpoints.LegalParameters ε X H h₀)
    {h : ℤ} (hh : h ∈ PrimePairEndpoints.translatedWindow H h₀) :
    (h.natAbs : ℝ) ≤ 2 * Real.rpow X (1 - ε) := by
  have hbounds :=
    (PrimePairEndpoints.mem_translatedWindow_iff_real_bounds.mp hh)
  rcases hlegal with ⟨_hlower, hHupper, hh₀nonneg, hh₀upper⟩
  have habs : |(h : ℝ)| ≤ h₀ + H := by
    rw [abs_le]
    constructor <;> linarith
  have heq : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_abs]
    norm_num
  rw [heq]
  exact habs.trans (by linarith)
/-- The lower aperture condition forces a legal window to have length at
least one once `X ≥ 1`. -/
theorem one_le_H_of_legal
    {X H h₀ ε : ℝ} (hX : 1 ≤ X) (hε : 0 < ε)
    (hlegal : PrimePairEndpoints.LegalParameters ε X H h₀) :
    1 ≤ H := by
  have hexp : 0 ≤ 2 / 15 + ε := by linarith
  have hrpow : 1 ≤ Real.rpow X (2 / 15 + ε) :=
    Real.one_le_rpow hX hexp
  exact hrpow.trans hlegal.1
/-- Eventually the whole legal translated shift range lies in `|h| < X`,
which is the exact domain of the pointwise collar estimate. -/
theorem eventually_two_rpow_one_sub_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      2 * Real.rpow X (1 - ε) < X := by
  have hlarge : ∀ᶠ X : ℝ in Filter.atTop, 2 < Real.rpow X ε :=
    (tendsto_rpow_atTop hε).eventually (Filter.eventually_gt_atTop 2)
  filter_upwards [hlarge, Filter.eventually_gt_atTop 0] with X hpow hX
  have hpos : 0 < Real.rpow X (1 - ε) := Real.rpow_pos_of_pos hX _
  have hmul := mul_lt_mul_of_pos_left hpow hpos
  calc
    2 * Real.rpow X (1 - ε) = Real.rpow X (1 - ε) * 2 := by ring
    _ < Real.rpow X (1 - ε) * Real.rpow X ε := hmul
    _ = Real.rpow X ((1 - ε) + ε) := (Real.rpow_add hX _ _).symm
    _ = X := by ring_nf; simp
end
end SupportBoundaryQuantitative

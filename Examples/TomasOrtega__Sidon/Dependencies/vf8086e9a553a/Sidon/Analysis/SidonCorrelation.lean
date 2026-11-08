module
public import Examples.TomasOrtega__Sidon.Dependencies.vf8086e9a553a.Sidon.Analysis.VanDerCorput
public import Examples.TomasOrtega__Sidon.Dependencies.vf8086e9a553a.Sidon.Combinatorics.IntervalSize
public import Mathlib.Tactic
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-! # Correlation estimates for a Sidon set and its interval model -/
noncomputable section
open scoped ComplexConjugate
namespace Sidon
def intervalModel (N : ℕ) (S : Finset ℤ) : ℤ →₀ ℂ :=
  ((S.card : ℝ) / N) • indicatorFinsupp (interval N)
def correlationError (N : ℕ) (S : Finset ℤ) (H : ℕ) (f g : ℤ →₀ ℂ) : ℝ :=
  (fejerWeight H).sum
    (fun h w => w * |(S.card : ℝ) ^ 2 / N - (correlation f g h).re|)
def boundaryPart (N : ℕ) (S : Finset ℤ) (h : ℤ) : Finset ℤ :=
  S.filter fun x => x + h ∉ interval N
theorem correlation_indicatorFinsupp (S T : Finset ℤ) (h : ℤ) :
    correlation (indicatorFinsupp S) (indicatorFinsupp T) h =
      (((S.filter fun x => x + h ∈ T).card : ℕ) : ℂ) := by
  classical
  rw [correlation, Finsupp.sum, support_indicatorFinsupp, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x hx
  simp [indicatorFinsupp_apply, hx]
theorem re_correlation_indicatorFinsupp (S T : Finset ℤ) (h : ℤ) :
    (correlation (indicatorFinsupp S) (indicatorFinsupp T) h).re =
      ((S.filter fun x => x + h ∈ T).card : ℝ) := by
  rw [correlation_indicatorFinsupp]
  simp
theorem boundaryPart_card_add (N : ℕ) (S : Finset ℤ) (h : ℤ) :
    (S.filter fun x => x + h ∈ interval N).card + (boundaryPart N S h).card =
      S.card := by
  exact Finset.card_filter_add_card_filter_not _
theorem re_correlation_intervalModel_right (N : ℕ) (S : Finset ℤ) (h : ℤ) :
    (correlation (indicatorFinsupp S) (intervalModel N S) h).re =
      ((S.card : ℝ) / N) * ((S.filter fun x => x + h ∈ interval N).card : ℝ) := by
  rw [intervalModel, correlation_real_smul_right, Complex.smul_re,
    re_correlation_indicatorFinsupp]
  rfl
theorem intervalModel_mixed_deficit (N : ℕ) (S : Finset ℤ) (h : ℤ) :
    |(S.card : ℝ) ^ 2 / N -
        (correlation (indicatorFinsupp S) (intervalModel N S) h).re| =
      ((S.card : ℝ) / N) * (boundaryPart N S h).card := by
  rw [re_correlation_intervalModel_right]
  have hcard : ((S.filter fun x => x + h ∈ interval N).card : ℝ) +
      (boundaryPart N S h).card = (S.card : ℝ) := by
    exact_mod_cast boundaryPart_card_add N S h
  have hnonneg : 0 ≤ ((S.card : ℝ) / N) * (boundaryPart N S h).card := by positivity
  have heq : (S.card : ℝ) ^ 2 / N -
      ((S.card : ℝ) / N) * ((S.filter fun x => x + h ∈ interval N).card : ℝ) =
      ((S.card : ℝ) / N) * (boundaryPart N S h).card := by
    rw [← hcard]
    ring
  rw [heq, abs_of_nonneg hnonneg]
theorem boundaryPart_card_le {N : ℕ} {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) (h : ℤ) :
    ((boundaryPart N S h).card : ℝ) ≤ 2 * Real.sqrt |(h : ℝ)| := by
  have hB : IsSidonSet ((boundaryPart N S h : Finset ℤ) : Set ℤ) :=
    hS.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have habs : ((h.natAbs : ℕ) : ℝ) = |(h : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [← habs]
  by_cases hh : 0 ≤ h
  · apply hB.card_le_two_mul_sqrt_of_subset_Icc ((N : ℤ) - h)
    intro x hx
    obtain ⟨hxS, hxn⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx₁, hx₂⟩ := mem_interval.mp (hSN hxS)
    have hneg : ¬ (1 ≤ x + h ∧ x + h ≤ N) := by simpa only [mem_interval] using hxn
    have hnat : (h.natAbs : ℤ) = h := by
      rw [Int.natCast_natAbs, abs_of_nonneg hh]
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · apply hB.card_le_two_mul_sqrt_of_subset_Icc 0
    intro x hx
    obtain ⟨hxS, hxn⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx₁, hx₂⟩ := mem_interval.mp (hSN hxS)
    have hneg : ¬ (1 ≤ x + h ∧ x + h ≤ N) := by simpa only [mem_interval] using hxn
    have hnat : (h.natAbs : ℤ) = -h := by
      rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hh)]
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
theorem mixed_correlationError_le {N H : ℕ} {S : Finset ℤ}
    (hH : 0 < H) (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    correlationError N S H (indicatorFinsupp S) (intervalModel N S) ≤
      2 * (S.card : ℝ) * Real.sqrt H / N := by
  unfold correlationError
  apply sum_fejerWeight_mul_le H hH
  intro h hh
  rw [intervalModel_mixed_deficit]
  have hbound := boundaryPart_card_le hS hSN h
  have habs : |(h : ℝ)| ≤ (H : ℝ) := by
    exact_mod_cast (abs_lt_of_mem_support_fejerWeight H hh).le
  have hsqrt := Real.sqrt_le_sqrt habs
  have hcoeff : 0 ≤ (S.card : ℝ) / N := by positivity
  calc
    ((S.card : ℝ) / N) * (boundaryPart N S h).card ≤
        ((S.card : ℝ) / N) * (2 * Real.sqrt |(h : ℝ)|) :=
      mul_le_mul_of_nonneg_left hbound hcoeff
    _ ≤ ((S.card : ℝ) / N) * (2 * Real.sqrt H) := by gcongr
    _ = 2 * (S.card : ℝ) * Real.sqrt H / N := by ring
end Sidon

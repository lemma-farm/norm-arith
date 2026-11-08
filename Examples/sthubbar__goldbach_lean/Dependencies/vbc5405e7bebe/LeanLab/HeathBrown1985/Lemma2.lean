module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.vbc5405e7bebe.LeanLab.HeathBrown1985.Elementary
/-!
P0096 Heath-Brown 1985, Lemma 2, 2.11, deduced from Lemma 1, 2.7, the bound 2.5 and the
divisor moments 2.2 with t = 2 and t = 3, following pages 50 to 52 of the paper.
The divisor moments are named inputs `DivMoment2` and `DivMoment3`.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
theorem sum_card_divisors_divisors_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ a ∈ m.divisors, (a.divisors.card : ℝ) ≤ (m.divisors.card : ℝ) ^ 2 := by
  calc ∑ a ∈ m.divisors, (a.divisors.card : ℝ) ≤ ∑ a ∈ m.divisors, (m.divisors.card : ℝ) := by
        apply sum_le_sum
        intro a ha
        have hdvd := Nat.dvd_of_mem_divisors ha
        exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd (by omega) hdvd)
    _ = _ := by rw [sum_const, nsmul_eq_mul, sq]
theorem mod_eq_iff_dvd_sub {m n h : ℕ} (hmn : m < n) : n % h = m % h ↔ h ∣ n - m := by
  rw [eq_comm]; exact Nat.modEq_iff_dvd' hmn.le
end LeanLab.HeathBrown1985

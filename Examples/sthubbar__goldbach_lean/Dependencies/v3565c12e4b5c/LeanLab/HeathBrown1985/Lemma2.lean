module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.Elementary
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
theorem abs_LambdaQ_le_cube (Q : ℝ) (hQ : 0 ≤ Q) (n : ℕ) : |LambdaQ Q n| ≤ Q ^ 3 := by
  unfold LambdaQ
  set F := ⌊Q⌋₊
  have hF : (F : ℝ) ≤ Q := Nat.floor_le hQ
  have hterm : ∀ q ∈ Icc 1 F, |((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
      ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)| ≤ (F : ℝ) ^ 2 := by
    intro q hq
    have hq1 := (mem_Icc.mp hq).1
    have hqF := (mem_Icc.mp hq).2
    have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hμ : (μ q : ℝ) ^ 2 ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := q)
      have h' : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast h
      nlinarith [abs_nonneg (μ q : ℝ), sq_abs (μ q : ℝ)]
    have hc : 0 ≤ (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) := by positivity
    have hc1 : (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have hg : n.gcd q ≤ q := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right n q)
    have hsum : |∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)| ≤ (F : ℝ) ^ 2 := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ d ∈ (n.gcd q).divisors, |(d : ℝ) * (μ d : ℝ)|
          ≤ ∑ d ∈ (n.gcd q).divisors, (F : ℝ) := by
            apply sum_le_sum; intro d hd
            rw [abs_mul, Nat.abs_cast]
            have h1 : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            have h2 : (d : ℝ) ≤ F := by
              exact_mod_cast (Nat.divisor_le hd).trans (hg.trans hqF)
            nlinarith [abs_nonneg (μ d : ℝ), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
        _ = ((n.gcd q).divisors.card : ℝ) * F := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (F : ℝ) * F := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast (Nat.card_divisors_le_self _).trans (hg.trans hqF)
        _ = _ := by ring
    rw [abs_mul, abs_of_nonneg hc]
    calc _ ≤ 1 * (F : ℝ) ^ 2 := mul_le_mul hc1 hsum (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  calc _ ≤ ∑ q ∈ Icc 1 F, |((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
        ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Icc 1 F, (F : ℝ) ^ 2 := sum_le_sum hterm
    _ = (F : ℝ) ^ 3 := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    _ ≤ Q ^ 3 := pow_le_pow_left₀ (by positivity) hF 3
end LeanLab.HeathBrown1985

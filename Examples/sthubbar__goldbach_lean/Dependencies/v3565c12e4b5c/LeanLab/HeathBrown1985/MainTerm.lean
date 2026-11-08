module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.MainTermLocal
public import Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.Theorem1Chain
/-!
P0096 Heath-Brown 1985, page 57, the main term: `MainTerm4` from 2.4, hence from the
Siegel-Walfisz theorem 1.1, and Theorem 1 from the bound for Σ₃ and Siegel-Walfisz.
For one `m`, 4.1 is `x Σ_{q ≤ Q} g_m(q) + O(x Q⁻¹)`, the tail of the singular series is
`O(x Q⁻¹ L d(m)²)` (2.3 in the form of `tail_gcd_le`), and the case `t = 2` of 2.2 sums
`d(m)²` over `m ≤ 3x`, giving `x² L⁴ Q⁻¹` in all.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
theorem abs_singular_le (m : ℕ) (hm : 1 ≤ m) :
    |singular m| ≤ 1 + 24 * (m.divisors.card : ℝ) ^ 2 := by
  have h := abs_singular_sub_le m 1 hm le_rfl
  have e : ∑ q ∈ Icc 1 1, gm m q = 1 := by simp [gm_one]
  rw [e] at h
  simp only [Nat.cast_one, Real.log_one, div_one] at h
  have := abs_sub_abs_le_abs_sub (singular m) 1
  rw [abs_one] at this
  nlinarith
/-- The crude bound for one `m`. -/
theorem per_m_crude (B x : ℝ) (hx : 2 ≤ x) (m : ℕ) (hm : m ∈ mRange x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (Real.log x ^ B) n * Λ (m - n) - x * singular m| ≤
      x * (Real.log x ^ B) ^ 3 * Real.log (3 * x) + x * (1 + 216 * x ^ 2) := by
  simp only [mRange, mem_filter, mem_Icc] at hm
  obtain ⟨⟨hm1, hm3⟩, _⟩ := hm
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set Q := Real.log x ^ B
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hL0 _
  have hmR : (m : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast hm3) (Nat.floor_le (by linarith))
  have hl3 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
  have hS : |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n)| ≤ x * Q ^ 3 * Real.log (3 * x) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hpt : ∀ n ∈ Icc 1 ⌊x⌋₊, |LambdaQ Q n * Λ (m - n)| ≤ Q ^ 3 * Real.log (3 * x) := by
      intro n _
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul (abs_LambdaQ_le_cube Q hQ0 n)
        (vonMangoldt_le_log_of_le _ _ (by linarith)
          (le_trans (by exact_mod_cast Nat.sub_le m n) hmR))
        ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    refine (sum_le_sum hpt).trans ?_
    rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le hx0.le)
      (by positivity)) hl3
  have hsing := abs_singular_le m hm1
  have hd : (m.divisors.card : ℝ) ≤ 3 * x :=
    le_trans (by exact_mod_cast Nat.card_divisors_le_self m) hmR
  have hd0 : (0 : ℝ) ≤ m.divisors.card := by positivity
  have hsing' : |singular m| ≤ 1 + 216 * x ^ 2 := by nlinarith
  calc _ ≤ |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n)| + |x * singular m| := abs_sub _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_pos hx0]
        have := mul_le_mul_of_nonneg_left hsing' hx0.le
        linarith
/-- **Bounded `x`**: the crude bound. -/
theorem mainTerm_small (B : ℝ) (hB : 0 < B) (X1 : ℝ) (hX1 : 3 ≤ X1) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → x ≤ X1 →
      ∑ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (Real.log x ^ B) n * Λ (m - n) -
        x * singular m| ≤ K * x ^ 2 * Real.log x ^ 4 / Real.log x ^ B := by
  set LX := Real.log X1
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  have hLX : l2 ≤ LX := Real.log_le_log (by norm_num) (by linarith)
  have hLX0 : 0 < LX := by linarith
  set C0 := X1 * (LX ^ B) ^ 3 * Real.log (3 * X1) + X1 * (1 + 216 * X1 ^ 2)
  have hC0 : 0 ≤ C0 := by
    have : 0 ≤ Real.log (3 * X1) := Real.log_nonneg (by linarith)
    have : 0 ≤ LX ^ B := Real.rpow_nonneg hLX0.le _
    positivity
  have hLXB : 0 < LX ^ B := Real.rpow_pos_of_pos hLX0 _
  refine ⟨3 * X1 * C0 * LX ^ B / (4 * l2 ^ 4), fun x hx hxX => ?_⟩
  have hx0 : 0 < x := by linarith
  set L := Real.log x
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  have hLLX : L ≤ LX := Real.log_le_log hx0 hxX
  have hQ : L ^ B ≤ LX ^ B := Real.rpow_le_rpow hL0.le hLLX hB.le
  have hQ0 : 0 < L ^ B := Real.rpow_pos_of_pos hL0 _
  have hper : ∀ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (L ^ B) n * Λ (m - n) -
      x * singular m| ≤ C0 := by
    intro m hm
    refine (per_m_crude B x hx m hm).trans ?_
    have h3 : Real.log (3 * x) ≤ Real.log (3 * X1) := Real.log_le_log (by linarith) (by linarith)
    have h3' : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
    have hQ3 : (L ^ B) ^ 3 ≤ (LX ^ B) ^ 3 := pow_le_pow_left₀ hQ0.le hQ 3
    have a1 : x * (L ^ B) ^ 3 * Real.log (3 * x) ≤ X1 * (LX ^ B) ^ 3 * Real.log (3 * X1) := by
      apply mul_le_mul (mul_le_mul hxX hQ3 (by positivity) (by linarith)) h3 h3'
        (by positivity)
    have a2 : x * (1 + 216 * x ^ 2) ≤ X1 * (1 + 216 * X1 ^ 2) := by
      apply mul_le_mul hxX _ (by positivity) (by linarith)
      nlinarith
    simp only [C0]; linarith
  refine (sum_le_sum hper).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hcard := card_mRange_le x hx0.le
  have h1 : (#(mRange x) : ℝ) * C0 ≤ 3 * X1 * C0 :=
    mul_le_mul_of_nonneg_right (hcard.trans (by linarith)) hC0
  refine h1.trans ?_
  have hL4 : l2 ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hl2.le hL2 4
  have hfac : 1 ≤ LX ^ B / (4 * l2 ^ 4) * (x ^ 2 * L ^ 4 / L ^ B) := by
    rw [div_mul_div_comm, le_div_iff₀ (by positivity), one_mul]
    have hx2 : 4 ≤ x ^ 2 := by nlinarith
    have := mul_le_mul hx2 hL4 (by positivity) (by positivity)
    calc 4 * l2 ^ 4 * L ^ B ≤ x ^ 2 * L ^ 4 * L ^ B :=
          mul_le_mul_of_nonneg_right (by linarith) hQ0.le
      _ ≤ x ^ 2 * L ^ 4 * LX ^ B := mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = LX ^ B * (x ^ 2 * L ^ 4) := by ring
  have h3X : 0 ≤ 3 * X1 * C0 := by positivity
  calc 3 * X1 * C0 = 3 * X1 * C0 * 1 := by ring
    _ ≤ 3 * X1 * C0 * (LX ^ B / (4 * l2 ^ 4) * (x ^ 2 * L ^ 4 / L ^ B)) :=
        mul_le_mul_of_nonneg_left hfac h3X
    _ = _ := by ring
end LeanLab.HeathBrown1985

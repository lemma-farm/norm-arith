module

public import Mathlib

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.ChenExplicit.Statements ====
public section
/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Explicit Chen theorems, statements only, as `Prop`s so that no placeholder proof is needed.
* P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409, Theorem 1.1.
* P0009 M. Bordignon, D. R. Johnston, V. Starichkova, An explicit version of Chen's theorem,
  arXiv 2207.09452, Theorem 3, Corollary 4, Theorem 5.
Both papers define their count as the number of representations of `N` as a prime plus a
product of at most two primes; neither text, as read on 2026-10-16, adds size conditions on the
prime factors, so we use `Nat.IsAtMostAlmostPrime 2` from Mathlib, which admits `1`.
-/
@[expose] public section
open Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega
noncomputable section
namespace LeanLab.ChenExplicit
def twinC : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)
end LeanLab.ChenExplicit

end
end
end

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.Statements ====
public section
/-!
P0096 D. R. Heath-Brown, The Ternary Goldbach Problem, Rev. Mat. Iberoam. 1 1985 45-59,
DOI 10.4171/RMI/2, read from the EMS scan 2026-10-16, pages 45 to 52.
STATED: the Siegel-Walfisz input 1.1, Theorem 1, Corollaries 1 to 3, Theorem 2, the function
Λ_Q, the bound 2.5, Lemma 1 as 2.6 and 2.7, Lemma 2 as 2.11. The paper's results are
classical and ineffective; here every analytic result is a `Prop`, no placeholder proof.
"≪" with constants depending on A, B, C is read as: for each such parameter some K, for
every x ≥ 2. L = log x throughout.
PROVED elsewhere in this folder: Corollary 1 from Theorem 1, Bridge.lean; Λ_Q in Ramanujan
sum form, Bridge.lean.
AI-written Lean code, Claude, run 20261016T2204Z-20593. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
def singular (m : ℕ) : ℝ :=
  if Even m then 2 * ChenExplicit.twinC *
    ∏ p ∈ m.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  else 0
def LambdaQ (Q : ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊Q⌋₊, ((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
    ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)
end LeanLab.HeathBrown1985

end
end
end

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.Section3 ====
public section
/-!
P0096 Heath-Brown 1985, section 3, pages 53 to 55: the sum
`Σ = Σ_{2x < m ≤ 3x} |Σ_{n ≤ x} Δ_Q(n) Λ(m - n)|` split by Vaughan's identity 3.1 with
`N = 3x`, `u = Q`, `v = x Q⁻²`, `f(n) = Δ_Q(m - n)` for `m - x ≤ n < m`, else `0`.
PROVED here: `Σ ≤ Σ₁ + Σ₂ + Σ₃`. STATED: the bounds (3.2) for Σ₁ and the bound for Σ₂.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
def mRange (x : ℝ) : Finset ℕ := (Icc 1 ⌊3 * x⌋₊).filter (fun m => 2 * x < (m : ℝ))
end LeanLab.HeathBrown1985

end
end
end

-- ==== Examples.sthubbar__goldbach_lean.Examples.Example_4b087e4cc21048686719_MainTerm ====
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


set_option linter.unusedVariables false in
/-- **Bounded `x`**: the crude bound. -/
theorem mainTerm_small (B : ℝ) (hB : 0 < B) (X1 : ℝ) (hX1 : 3 ≤ X1) 
    (h_LeanLab_HeathBrown1985_per_m_crude : ∀ (B x : ℝ),
      2 ≤ x →
        ∀ m ∈ LeanLab.HeathBrown1985.mRange x,
          |∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
                  LeanLab.HeathBrown1985.LambdaQ (Real.log x ^ B) n *
                    (ArithmeticFunction.vonMangoldt : ℕ → ℝ) (m - n) -
                x * LeanLab.HeathBrown1985.singular m| ≤
            x * (Real.log x ^ B) ^ 3 * Real.log (3 * x) + x * (1 + 216 * x ^ 2))
    (h_LeanLab_HeathBrown1985_card_mRange_le : ∀ (x : ℝ), 0 ≤ x → (↑(LeanLab.HeathBrown1985.mRange x).card : ℝ) ≤ 3 * x)
    :
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
    refine (h_LeanLab_HeathBrown1985_per_m_crude B x hx m hm).trans ?_
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
  have hcard := h_LeanLab_HeathBrown1985_card_mRange_le x hx0.le
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

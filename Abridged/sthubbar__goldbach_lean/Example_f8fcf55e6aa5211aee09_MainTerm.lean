module

public import Mathlib

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.vbc5405e7bebe.LeanLab.ChenExplicit.Statements ====
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

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.vbc5405e7bebe.LeanLab.HeathBrown1985.Statements ====
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
/-- `ψ(x; k, l) = Σ_{n ≤ x, n ≡ l mod k} Λ(n)`. -/
def psi (x : ℝ) (k l : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k), Λ n
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

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.vbc5405e7bebe.LeanLab.HeathBrown1985.Section3 ====
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

-- ==== Examples.sthubbar__goldbach_lean.Examples.Example_f8fcf55e6aa5211aee09_MainTerm ====
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
/-- **Large `x`**: the bound once `x ≥ 3`, `L ≥ 1` and `Q² ≤ x`. -/
theorem mainTerm_large (B : ℝ) (hB : 0 < B) (K4 : ℝ)
    (hK4 : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
      |psi x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)| ≤
        K4 * x * Real.log x ^ (-(2 * B + 2))) 
    (h_LeanLab_HeathBrown1985_tailterm_le : ∀ (B x : ℝ),
      0 < B →
        2 ≤ x →
          1 ≤ Real.log x ^ B →
            ∀ (D : ℝ),
              0 ≤ D →
                x * (4 * ((6 + 2 * Real.log (↑⌊Real.log x ^ B⌋₊ : ℝ)) * D / (↑⌊Real.log x ^ B⌋₊ : ℝ))) ≤
                  8 * (6 / Real.log 2 + 2 * B) * x * Real.log x * D / Real.log x ^ B)
    (h_LeanLab_HeathBrown1985_delta_le : ∀ (A B K4 x : ℝ),
      A = 2 * B + 2 →
        2 ≤ x →
          2 * (|K4| * (3 * x) * (Real.log x / 2) ^ (-A)) *
              (Real.log x ^ B * ((1 + Real.log x) * (Real.exp 1 * (1 + Real.log x / Real.log 2)))) ≤
            6 * |K4| * 2 ^ A * ((1 + 1 / Real.log 2) * (2 * Real.exp 1 / Real.log 2)) * x /
              Real.log x ^ B)
    (h_LeanLab_HeathBrown1985_per_m_bound : ∀ (A K4 : ℝ),
      0 < A →
        (∀ (x : ℝ),
            2 ≤ x →
              ∀ (k l : ℕ),
                1 ≤ k →
                  (↑k : ℝ) ≤ x →
                    |LeanLab.HeathBrown1985.psi x k l -
                          if l.Coprime k then x / (↑k.totient : ℝ) else 0| ≤
                      K4 * x * Real.log x ^ (-A)) →
          ∀ (x : ℝ),
            3 ≤ x →
              ∀ (Q : ℝ),
                1 ≤ Q →
                  Q ≤ x - 1 →
                    ∀ m ∈ LeanLab.HeathBrown1985.mRange x,
                      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
                              LeanLab.HeathBrown1985.LambdaQ Q n *
                                (ArithmeticFunction.vonMangoldt : ℕ → ℝ) (m - n) -
                            x * LeanLab.HeathBrown1985.singular m| ≤
                        2 * (|K4| * (3 * x) * (Real.log x / 2) ^ (-A)) *
                              (Q * ((1 + Real.log x) * (Real.exp 1 * (1 + Real.log x / Real.log 2)))) +
                            Q +
                          x *
                            (4 *
                              ((6 + 2 * Real.log (↑⌊Q⌋₊ : ℝ)) * (↑m.divisors.card : ℝ) ^ 2 /
                                (↑⌊Q⌋₊ : ℝ))))
    (h_LeanLab_HeathBrown1985_card_mRange_le : ∀ (x : ℝ), 0 ≤ x → (↑(LeanLab.HeathBrown1985.mRange x).card : ℝ) ≤ 3 * x)
    (h_LeanLab_HeathBrown1985_sum_dsq_mRange_le : ∀ (x : ℝ),
      2 ≤ x →
        ∑ m ∈ LeanLab.HeathBrown1985.mRange x, (↑m.divisors.card : ℝ) ^ 2 ≤ 648 * x * Real.log x ^ 3)
    :
    ∃ K : ℝ, ∀ x : ℝ, 3 ≤ x → 1 ≤ Real.log x → (Real.log x ^ B) ^ 2 ≤ x →
      ∑ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (Real.log x ^ B) n * Λ (m - n) -
        x * singular m| ≤ K * x ^ 2 * Real.log x ^ 4 / Real.log x ^ B := by
  set c1 := 6 * |K4| * 2 ^ (2 * B + 2) * ((1 + 1 / Real.log 2) * (2 * Real.exp 1 / Real.log 2))
  set c3 := 8 * (6 / Real.log 2 + 2 * B)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc1 : 0 ≤ c1 := by positivity
  have hc3 : 0 ≤ c3 := by positivity
  refine ⟨3 * (c1 + 1) + 648 * c3, fun x hx hL1 hQx => ?_⟩
  set L := Real.log x
  set Q := L ^ B
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := by linarith
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hL1 hB.le
  have hQ0 : 0 < Q := by linarith
  have hQx1 : Q ≤ x - 1 := by
    by_contra h
    have h' : x - 1 < Q := lt_of_not_ge h
    nlinarith
  have hQxQ : Q ≤ x / Q := by rw [le_div_iff₀ hQ0]; nlinarith
  have hper : ∀ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n) - x * singular m| ≤
      (c1 + 1) * (x / Q) + c3 * x * L / Q * (m.divisors.card : ℝ) ^ 2 := by
    intro m hm
    have h := h_LeanLab_HeathBrown1985_per_m_bound (2 * B + 2) K4 (by linarith) hK4 x hx Q hQ1 hQx1 m hm
    have hd := h_LeanLab_HeathBrown1985_delta_le (2 * B + 2) B K4 x rfl (by linarith)
    have ht := h_LeanLab_HeathBrown1985_tailterm_le B x hB (by linarith) hQ1 ((m.divisors.card : ℝ) ^ 2) (by positivity)
    have e1 : c1 * x / Q = c1 * (x / Q) := by ring
    have e3 : c3 * x * L * (m.divisors.card : ℝ) ^ 2 / Q =
        c3 * x * L / Q * (m.divisors.card : ℝ) ^ 2 := by ring
    linarith
  refine (sum_le_sum hper).trans ?_
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
  have hcard := h_LeanLab_HeathBrown1985_card_mRange_le x hx0.le
  have hdsq := h_LeanLab_HeathBrown1985_sum_dsq_mRange_le x (by linarith)
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hxQ : 0 ≤ x / Q := by positivity
  have hcx : 0 ≤ c3 * x * L / Q := by positivity
  calc (#(mRange x) : ℝ) * ((c1 + 1) * (x / Q)) + c3 * x * L / Q *
        ∑ m ∈ mRange x, (m.divisors.card : ℝ) ^ 2
      ≤ 3 * x * ((c1 + 1) * (x / Q)) + c3 * x * L / Q * (648 * x * L ^ 3) := by
        gcongr
    _ = (3 * (c1 + 1) * 1 + 648 * c3 * L ^ 4) * (x ^ 2 / Q) := by ring
    _ ≤ (3 * (c1 + 1) * L ^ 4 + 648 * c3 * L ^ 4) * (x ^ 2 / Q) := by
        gcongr
    _ = _ := by ring
end LeanLab.HeathBrown1985

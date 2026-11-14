module

public import Mathlib

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.ChenExplicit.Statements ====
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

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.HeathBrown1985.Statements ====
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

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.HeathBrown1985.SingularSeries ====
public section
/-!
P0096 Heath-Brown 1985, page 57, the singular series: the function
`g_m(q) = μ(q)²/φ(q) Σ_{d ∣ q} d μ(d) E_{d,m}/φ(d)`, its product form
`Π_{p ∣ q} (1 - p E_{p,m}/(p-1))/(p-1)` for squarefree `q`, the bound
`|g_m(q)| ≤ 4 (q, m) d(q) q⁻²` (the paper's `(q,m)/φ(q)² ≪ (q,m) d(q)/q²`), the tail
`Σ_{q > F} (q, m) d(q) q⁻² ≤ (6 + 2 log F) d(m)²/F` (the paper's use of 2.3), and the Euler
product `Σ_q g_m(q) = 𝔖(m)` for `m ≥ 1`.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
/-- `E_{d,m} = 1` if `(d, m) = 1`, else `0`. -/
def Ecop (d m : ℕ) : ℝ := if Nat.Coprime m d then 1 else 0

/-- `g_m(q) = μ(q)²/φ(q) Σ_{d ∣ q} d μ(d) E_{d,m}/φ(d)`, the `q`-term of the main term, page 57. -/
def gm (m q : ℕ) : ℝ :=
  (μ q : ℝ) ^ 2 / (Nat.totient q : ℝ) *
    ∑ d ∈ q.divisors, (d : ℝ) * (μ d : ℝ) * Ecop d m / (Nat.totient d : ℝ)

/-! ### `|g_m(q)| ≤ 4 (q, m) d(q) / q²` -/

/-! ### Tail sums -/

/-! ### Summability and the Euler product -/

end LeanLab.HeathBrown1985

end
end
end

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.HeathBrown1985.Section3 ====
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

-- ==== Examples.sthubbar__goldbach_lean.Examples.Example_3dc4d789cb200e94c86d_MainTerm ====
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
/-- One `m`: `|Σ_{n ≤ x} Λ_Q(n) Λ(m - n) - x 𝔖(m)| ≤ δ + Q + 4x (6 + 2 log F) d(m)²/F`,
`F = ⌊Q⌋`, `δ` the local error. -/
theorem per_m_bound (A K4 : ℝ) (hA : 0 < A)
    (hK4 : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
      |psi x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)| ≤
        K4 * x * Real.log x ^ (-A))
    (x : ℝ) (hx : 3 ≤ x) (Q : ℝ) (hQ1 : 1 ≤ Q) (hQx : Q ≤ x - 1) (m : ℕ) (hm : m ∈ mRange x) 
    (h_LeanLab_HeathBrown1985_abs_singular_sub_le : ∀ (m F : ℕ),
      1 ≤ m →
        1 ≤ F →
          |LeanLab.HeathBrown1985.singular m - ∑ q ∈ Finset.Icc 1 F, LeanLab.HeathBrown1985.gm m q| ≤
            4 * ((6 + 2 * Real.log (↑F : ℝ)) * (↑m.divisors.card : ℝ) ^ 2 / (↑F : ℝ)))
    (h_LeanLab_HeathBrown1985_abs_gm_le_one : ∀ (m q : ℕ), |LeanLab.HeathBrown1985.gm m q| ≤ 1)
    (h_LeanLab_HeathBrown1985_local_expansion : ∀ (A K4 : ℝ),
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
                            (↑⌊x⌋₊ : ℝ) * ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, LeanLab.HeathBrown1985.gm m q| ≤
                        2 * (|K4| * (3 * x) * (Real.log x / 2) ^ (-A)) *
                          (Q * ((1 + Real.log x) * (Real.exp 1 * (1 + Real.log x / Real.log 2)))))
    :
    |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n) - x * singular m| ≤
      2 * (|K4| * (3 * x) * (Real.log x / 2) ^ (-A)) *
        (Q * ((1 + Real.log x) * (Real.exp 1 * (1 + Real.log x / Real.log 2)))) + Q +
      x * (4 * ((6 + 2 * Real.log ⌊Q⌋₊) * (m.divisors.card : ℝ) ^ 2 / ⌊Q⌋₊)) := by
  have hloc := h_LeanLab_HeathBrown1985_local_expansion A K4 hA hK4 x hx Q hQ1 hQx m hm
  have hm1 : 1 ≤ m := by simp only [mRange, mem_filter, mem_Icc] at hm; exact hm.1.1
  set F := ⌊Q⌋₊
  have hF1 : 1 ≤ F := Nat.le_floor (by exact_mod_cast hQ1)
  have hF : (F : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have htail := h_LeanLab_HeathBrown1985_abs_singular_sub_le m F hm1 hF1
  set S := ∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n)
  set Mf := ∑ q ∈ Icc 1 F, gm m q
  have hMf : |Mf| ≤ Q := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum (fun q _ => h_LeanLab_HeathBrown1985_abs_gm_le_one m q)).trans ?_
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
    exact hF
  have hx0 : 0 < x := by linarith
  have hN1 : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [Nat.lt_floor_add_one x]
    · linarith [Nat.floor_le hx0.le]
  have e : S - x * singular m = (S - ⌊x⌋₊ * Mf) + ((⌊x⌋₊ : ℝ) - x) * Mf +
      x * -(singular m - Mf) := by ring
  rw [e]
  have h2 : |((⌊x⌋₊ : ℝ) - x) * Mf| ≤ Q := by
    rw [abs_mul]
    calc |(⌊x⌋₊ : ℝ) - x| * |Mf| ≤ 1 * Q :=
          mul_le_mul hN1 hMf (abs_nonneg _) zero_le_one
      _ = Q := one_mul Q
  have h3 : |x * -(singular m - Mf)| ≤
      x * (4 * ((6 + 2 * Real.log F) * (m.divisors.card : ℝ) ^ 2 / F)) := by
    rw [abs_mul, abs_neg, abs_of_pos hx0]
    exact mul_le_mul_of_nonneg_left htail hx0.le
  calc _ ≤ |S - ⌊x⌋₊ * Mf + ((⌊x⌋₊ : ℝ) - x) * Mf| + |x * -(singular m - Mf)| := abs_add_le _ _
    _ ≤ |S - ⌊x⌋₊ * Mf| + |((⌊x⌋₊ : ℝ) - x) * Mf| + |x * -(singular m - Mf)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith
end LeanLab.HeathBrown1985

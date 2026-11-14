module

public import Mathlib

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.vd4887828222f.LeanLab.HeathBrown1985.Statements ====
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
def LambdaQ (Q : ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊Q⌋₊, ((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
    ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)
def DeltaQ (Q : ℝ) (n : ℕ) : ℝ := LambdaQ Q n - Λ n
/-- `Σ_{n ≤ x, n ≡ l mod k} f(n)`. -/
def apSum (f : ℕ → ℝ) (x : ℝ) (k l : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k), f n
def delta1 (x : ℝ) (k : ℕ) (Q : ℝ) : ℝ := ∑ l ∈ Icc 1 k, |apSum (DeltaQ Q) x k l|
end LeanLab.HeathBrown1985

end
end
end

-- ==== Examples.sthubbar__goldbach_lean.Examples.Example_9d3935edd02043640b72_Lemma2 ====
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
def resSum (f : ℕ → ℝ) (N k r : ℕ) : ℝ := ∑ n ∈ (Icc 1 N).filter (fun n => n % k = r), f n

/-! ### Averaging over multiples, page 51 -/

/-! ### Cauchy's inequality twice, 2.12 to 2.13 -/
/-- `δ₂` in residue form. -/
def delta2 (f : ℕ → ℝ) (N h : ℕ) : ℝ := ∑ r ∈ range h, (resSum f N h r) ^ 2


set_option linter.unusedVariables false in
theorem cauchy_main (x Q : ℝ) (M : ℕ) (hM : 1 ≤ M) (W : ℝ)
    (hW : ∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) ^ 2 ≤ W) 
    (h_LeanLab_HeathBrown1985_sum_avg : ∀ (x Q : ℝ) (M : ℕ),
      1 ≤ M →
        ∑ k ∈ Finset.Icc 1 M, LeanLab.HeathBrown1985.delta1 x k Q / (↑k : ℝ) ≤
          2 / (↑M : ℝ) *
            ∑ h ∈ Finset.Ioc M (2 * M), (↑h.divisors.card : ℝ) * LeanLab.HeathBrown1985.delta1 x h Q)
    (h_LeanLab_HeathBrown1985_delta2_nonneg : ∀ (f : ℕ → ℝ) (N h : ℕ), 0 ≤ LeanLab.HeathBrown1985.delta2 f N h)
    (h_LeanLab_HeathBrown1985_delta1_nonneg : ∀ (x : ℝ) (k : ℕ) (Q : ℝ), 0 ≤ LeanLab.HeathBrown1985.delta1 x k Q)
    (h_LeanLab_HeathBrown1985_delta1_sq_le : ∀ (x : ℝ) (h : ℕ) (Q : ℝ),
      1 ≤ h →
        LeanLab.HeathBrown1985.delta1 x h Q ^ 2 ≤
          (↑h : ℝ) * LeanLab.HeathBrown1985.delta2 (LeanLab.HeathBrown1985.DeltaQ Q) ⌊x⌋₊ h)
    :
    (∑ k ∈ Icc 1 M, delta1 x k Q / k) ^ 2 ≤
      (4 / (M : ℝ) ^ 2) * W * (2 * M * ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) ⌊x⌋₊ h) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set T := ∑ k ∈ Icc 1 M, delta1 x k Q / k
  set U := ∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) * delta1 x h Q
  have hT0 : 0 ≤ T := sum_nonneg (fun k _ => div_nonneg (h_LeanLab_HeathBrown1985_delta1_nonneg _ _ _) (by positivity))
  have hTU : T ≤ (2 / M) * U := h_LeanLab_HeathBrown1985_sum_avg x Q M hM
  have hU2 : U ^ 2 ≤ (∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) ^ 2) *
      ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
  have hd1 : ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2 ≤
      2 * M * ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) ⌊x⌋₊ h := by
    rw [mul_sum]; apply sum_le_sum; intro h hh
    simp only [mem_Ioc] at hh
    refine (h_LeanLab_HeathBrown1985_delta1_sq_le x h Q (by omega)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (h_LeanLab_HeathBrown1985_delta2_nonneg _ _ _)
    exact_mod_cast hh.2
  have hS0 : 0 ≤ ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hW0 : 0 ≤ W := le_trans (sum_nonneg (fun _ _ => sq_nonneg _)) hW
  calc T ^ 2 ≤ ((2 / M) * U) ^ 2 := pow_le_pow_left₀ hT0 hTU 2
    _ = (4 / (M : ℝ) ^ 2) * U ^ 2 := by ring
    _ ≤ (4 / (M : ℝ) ^ 2) * ((∑ h ∈ Ioc M (2 * M), (h.divisors.card : ℝ) ^ 2) *
          ∑ h ∈ Ioc M (2 * M), delta1 x h Q ^ 2) :=
        mul_le_mul_of_nonneg_left hU2 (by positivity)
    _ ≤ (4 / (M : ℝ) ^ 2) * (W * (2 * M * ∑ h ∈ Ioc M (2 * M), delta2 (DeltaQ Q) ⌊x⌋₊ h)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hW hd1 hS0 hW0
    _ = _ := by ring
/-! ### Expanding `δ₂`, 2.14 -/
end LeanLab.HeathBrown1985

module

public import Mathlib

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.vdcb372dc19bc.LeanLab.HeathBrown1985.Statements ====
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

-- ==== Examples.sthubbar__goldbach_lean.Examples.Example_82a86ad1a1050fb6ab94_Lemma2 ====
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
theorem delta1_div_le (x Q : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    delta1 x k Q / k ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q n| := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_iff₀ hkR]
  unfold delta1 apSum
  calc ∑ l ∈ Icc 1 k, |∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k), DeltaQ Q n|
      ≤ ∑ l ∈ Icc 1 k, ∑ n ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q n| := by
        apply sum_le_sum; intro l _
        refine (abs_sum_le_sum_abs _ _).trans ?_
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
    _ = _ := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
end LeanLab.HeathBrown1985

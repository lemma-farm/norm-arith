module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib
public import Mathlib.Algebra.Order.Chebyshev

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.v15aaf153db63.LeanLab.PNTPort.Vinogradov.SingPos ====
public section
/-!
# The ternary singular series: multiplicativity

Lab proof, unit U-5259. AI wrote this file. Known mathematics, no cited input.

* `gDiv n d = d · 1_{d ∣ n}`, multiplicative; `cR n = gDiv n * μ`, the Ramanujan sum
  `c_q(n)` as a Dirichlet convolution, multiplicative, `cR_apply`.
* `fS n q = μ(q) c_q(n) / φ(q)³`, multiplicative, `fS_mult`.
-/
@[expose] public section
namespace LeanLab.PNTPort.Vinogradov
open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
/-- `d ↦ d · 1_{d ∣ n}`. -/
noncomputable def gDiv (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d ∣ n then (d : ℝ) else 0, by simp⟩

/-- The Ramanujan sum as a Dirichlet convolution. -/
noncomputable def cR (n : ℕ) : ArithmeticFunction ℝ := gDiv n * (μ : ArithmeticFunction ℝ)

/-- `q ↦ 1/φ(q)³`. -/
noncomputable def invPhi3 : ArithmeticFunction ℝ := ⟨fun q => 1 / (q.totient : ℝ) ^ 3, by simp⟩

/-- The factor `f(q) = μ(q) c_q(n) / φ(q)³`. -/
noncomputable def fS (n : ℕ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ).pmul (cR n)).pmul invPhi3

end LeanLab.PNTPort.Vinogradov

end
end

-- ==== Examples.sthubbar__goldbach_lean.Dependencies.v15aaf153db63.LeanLab.VanDerCorput1939.Statements ====
public section
/-!
P0067 J. G. van der Corput, Sur la démonstration de l'hypothèse de Goldbach pour les nombres
impairs, donnée par M. Vinogradow, Bull. Soc. Math. France 67 1939, supplément, 87-99,
a lecture of 8 July 1937. Read from the numdam scan, pages 87 to 94, run 20261016T2204Z-20593.
STATED: Vinogradov's asymptotic (1) to (3) for I(N), the number of ways to write odd N as a sum
of three primes, as van der Corput reports it.
PROVED, no gaps: the Euler factor identity (1 + 1/(p-1)³)(1 - 1/(p² - 3p + 3)) = 1 - 1/(p-1)²,
prime by prime; the global identity of K P(N) with the singular series is NOT formalized;
K ≥ 1; that (1) gives every large odd N as a sum of three primes; and, in Totient.lean, the
lecture's φ(q) ≥ (1/2) q^{3/4}.
Not stated: the major and minor arc estimates of pages 91 to 99, whose constants c_m, γ_i
are not explicit.
AI-written Lean code, Claude. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013.
-/
@[expose] public section
noncomputable section
namespace LeanLab.VanDerCorput1939
open Real Finset
attribute [local instance] Classical.propDecidable

/-- (2) `K = ∏_p (1 + 1/(p-1)³)` over all primes. -/
def K : ℝ := ∏' p : {p : ℕ // p.Prime}, (1 + 1 / ((p : ℝ) - 1) ^ 3)
/-- (3) `P(N) = ∏_{p ∣ N} (1 - 1/(p² - 3p + 3))`. -/
def P (N : ℕ) : ℝ := ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3))

/-! ### The Euler factors -/

end LeanLab.VanDerCorput1939

end
end
end

-- ==== Examples.sthubbar__goldbach_lean.Examples.Example_955cd7adec9122109f83_SingLimit ====
/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5704, paper P0067.
P0067 van der Corput 1939: the truncated ternary singular series tends to K P(N),
uniformly over odd N. For every ε > 0 there is P₀ with
|∑_{q ≤ Q} f_N(q) - K P(N)| ≤ ε for all Q ≥ P₀ and all odd N with log N ≤ Q,
where f_N(q) = μ(q) c_q(N)/φ(q)³ is `LeanLab.PNTPort.Vinogradov.fS N q`.
The proof gives the bound e⁸/√Q + |A_Q - K| + K/(Q - 1), with A_Q the partial Euler product
of K over primes up to Q; the hypothesis log N ≤ Q is not needed and is carried only to match
the stated form. No cited input. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013. Binary Goldbach is OPEN.
-/
@[expose] public section
noncomputable section
namespace LeanLab.VanDerCorput1939
open Real Finset Filter Topology
open LeanLab.PNTPort.Vinogradov
attribute [local instance] Classical.propDecidable
/-- The local factor of `P(N)`. -/
def cP (N p : ℕ) : ℝ := if p ∣ N then 1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3) else 1
/-- The partial Euler product of `K`. -/
def AK (Q : ℕ) : ℝ := ∏ p ∈ Nat.primesLE Q, (1 + 1 / ((p : ℝ) - 1) ^ 3)
/-- The partial product of `P(N)` over primes up to `Q`. -/
def BP (N Q : ℕ) : ℝ := ∏ p ∈ Nat.primesLE Q, cP N p


set_option linter.unusedVariables false in
/-- Step 6, the quantitative bound. -/
theorem abs_sum_fS_sub_KP_le {N Q : ℕ} (hN : Odd N) (hQ : 2 ≤ Q) 
    (h_LeanLab_VanDerCorput1939_BP_sub_P : ∀ {N Q : ℕ},
      Odd N →
        2 ≤ Q →
          0 ≤ LeanLab.VanDerCorput1939.BP N Q ∧
            LeanLab.VanDerCorput1939.BP N Q ≤ 1 ∧
              |LeanLab.VanDerCorput1939.BP N Q - LeanLab.VanDerCorput1939.P N| ≤ 1 / ((↑Q : ℝ) - 1))
    (h_LeanLab_VanDerCorput1939_K_gt : 2.29 < LeanLab.VanDerCorput1939.K)
    (h_LeanLab_VanDerCorput1939_abs_sum_fS_sub_euler : ∀ (n : ℕ) {Q : ℕ},
      1 ≤ Q →
        |∑ q ∈ Finset.Icc 1 Q, (LeanLab.PNTPort.Vinogradov.fS n : ℕ → ℝ) q -
              ∏ p ∈ Q.primesLE, (1 + (LeanLab.PNTPort.Vinogradov.fS n : ℕ → ℝ) p)| ≤
          Real.exp 8 / √(↑Q : ℝ))
    (h_LeanLab_VanDerCorput1939_euler_eq_AK_mul_BP : ∀ (N Q : ℕ),
      ∏ p ∈ Q.primesLE, (1 + (LeanLab.PNTPort.Vinogradov.fS N : ℕ → ℝ) p) =
        LeanLab.VanDerCorput1939.AK Q * LeanLab.VanDerCorput1939.BP N Q)
    :
    |∑ q ∈ Icc 1 Q, fS N q - K * P N| ≤
      Real.exp 8 / Real.sqrt Q + |AK Q - K| + K / ((Q : ℝ) - 1) := by
  have h1 := h_LeanLab_VanDerCorput1939_abs_sum_fS_sub_euler N (by omega : 1 ≤ Q)
  rw [h_LeanLab_VanDerCorput1939_euler_eq_AK_mul_BP] at h1
  obtain ⟨hB0, hB1, hBP⟩ := h_LeanLab_VanDerCorput1939_BP_sub_P hN hQ
  have hK : 0 < K := lt_trans (by norm_num) h_LeanLab_VanDerCorput1939_K_gt
  have e : ∑ q ∈ Icc 1 Q, fS N q - K * P N =
      (∑ q ∈ Icc 1 Q, fS N q - AK Q * BP N Q) + (AK Q - K) * BP N Q +
        K * (BP N Q - P N) := by ring
  rw [e]
  have h2 : |(AK Q - K) * BP N Q| ≤ |AK Q - K| := by
    rw [abs_mul, abs_of_nonneg hB0]
    calc |AK Q - K| * BP N Q ≤ |AK Q - K| * 1 := mul_le_mul_of_nonneg_left hB1 (abs_nonneg _)
      _ = |AK Q - K| := mul_one _
  have h3 : |K * (BP N Q - P N)| ≤ K / ((Q : ℝ) - 1) := by
    rw [abs_mul, abs_of_pos hK, mul_comm]
    calc |BP N Q - P N| * K ≤ 1 / ((Q : ℝ) - 1) * K := mul_le_mul_of_nonneg_right hBP hK.le
      _ = K / ((Q : ℝ) - 1) := by ring
  calc _ ≤ |∑ q ∈ Icc 1 Q, fS N q - AK Q * BP N Q| + |(AK Q - K) * BP N Q| +
        |K * (BP N Q - P N)| := abs_add_three _ _ _
    _ ≤ _ := by linarith

end LeanLab.VanDerCorput1939

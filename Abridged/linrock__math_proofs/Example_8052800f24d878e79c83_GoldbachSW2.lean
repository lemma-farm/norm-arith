module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_8052800f24d878e79c83_GoldbachSW2 ====
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
set_option maxHeartbeats 4000000
/-! ### ================= SiegelTheorem.lean (verbatim, deduplicated) ================= -/
set_option maxHeartbeats 2000000
/-!
# Siegel's theorem for Dirichlet L-functions — brick-by-brick (Goldfeld's route)

Target: `siegel_zero_free`: ∀ ε > 0, ∃ c(ε) > 0, every real zero β of every L(·,χ)
(χ real nontrivial mod q) satisfies β ≤ 1 − c(ε)/q^ε. Ineffective (the dichotomy
case-split is classical); the last missing zero-free input for Siegel–Walfisz and
hence for almost-all binary Goldbach (see the approved roadmap plan).

Phase A of the roadmap; every lemma verified 0-error + `#print axioms`-clean
([propext, Classical.choice, Quot.sound]) before banking.
-/
open PowerSeries ArithmeticFunction Finset Filter
/-- A bare function packaged as an arithmetic function (forcing the value 0 at 0). -/
noncomputable def toArith (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else g n, by simp⟩


/-- Convolution values are divisor-counted (Siegel brick A2e-iii-a1): for 1-bounded
    inputs, `|(k₁⋆k₂)(n)| ≤ τ(n)` where `τ(n) = #divisorsAntidiagonal(n)`. -/
lemma conv_value_le_tau (k₁ k₂ : ℕ → ℝ) (h1b : ∀ n, |k₁ n| ≤ 1) (h2b : ∀ n, |k₂ n| ≤ 1)
    (n : ℕ) :
    |(toArith k₁ * toArith k₂) n| ≤ ((n.divisorsAntidiagonal).card : ℝ) := by
  rw [ArithmeticFunction.mul_apply]
  calc |∑ p ∈ n.divisorsAntidiagonal, toArith k₁ p.1 * toArith k₂ p.2|
      ≤ ∑ p ∈ n.divisorsAntidiagonal, |toArith k₁ p.1 * toArith k₂ p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul]
        have h1 : |toArith k₁ p.1| ≤ 1 := by
          rcases Nat.eq_zero_or_pos p.1 with h0 | h0
          · simp [toArith, h0]
          · rw [show toArith k₁ p.1 = k₁ p.1 from by simp [toArith, h0.ne']]
            exact h1b p.1
        have h2 : |toArith k₂ p.2| ≤ 1 := by
          rcases Nat.eq_zero_or_pos p.2 with h0 | h0
          · simp [toArith, h0]
          · rw [show toArith k₂ p.2 = k₂ p.2 from by simp [toArith, h0.ne']]
            exact h2b p.2
        calc |toArith k₁ p.1| * |toArith k₂ p.2| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = ((n.divisorsAntidiagonal).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/


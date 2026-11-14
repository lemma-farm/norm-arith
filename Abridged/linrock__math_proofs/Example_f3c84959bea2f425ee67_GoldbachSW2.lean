module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_f3c84959bea2f425ee67_GoldbachSW2 ====
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


set_option linter.unusedVariables false in
/-- **The bounded-sum Abel tail bound** (Siegel brick A2c-i): if all partial sums of `g`
    are bounded by `q`, the tail `Σ_{y<d≤z} g(d)/d` is at most `2q/(y+1)` — uniformly
    in `z`. The engine of both `Σ_{d≤y} g(d)/d`'s convergence and its tail rate. -/
lemma abel_tail_bound (g : ℕ → ℝ) (q : ℝ)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q) (y z : ℕ) (hyz : y ≤ z) 
    (h_abel_window : ∀ (g : ℕ → ℝ) (y z : ℕ),
      y ≤ z →
        ∑ d ∈ Finset.Icc (y + 1) z, g d / (↑d : ℝ) =
          ∑ d ∈ Finset.Icc (y + 1) z,
                (∑ n ∈ Finset.Icc 1 d, g n) * (1 / (↑d : ℝ) - 1 / ((↑d : ℝ) + 1)) +
              (∑ n ∈ Finset.Icc 1 z, g n) / ((↑z : ℝ) + 1) -
            (∑ n ∈ Finset.Icc 1 y, g n) / ((↑y : ℝ) + 1))
    (h_telescope_kernel : ∀ (y z : ℕ),
      y ≤ z →
        ∑ d ∈ Finset.Icc (y + 1) z, (1 / (↑d : ℝ) - 1 / ((↑d : ℝ) + 1)) =
          1 / ((↑y : ℝ) + 1) - 1 / ((↑z : ℝ) + 1))
    :
    |∑ d ∈ Icc (y + 1) z, g d / d| ≤ 2 * q / (y + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  rw [h_abel_window g y z hyz]
  have hterm : ∀ d ∈ Icc (y + 1) z,
      |(∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
        ≤ q * ((1 : ℝ) / d - 1 / (d + 1)) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by
      have : (1:ℕ) ≤ d := by omega
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hker : (0:ℝ) ≤ 1 / (d : ℝ) - 1 / (d + 1) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) hd0]
      linarith
    rw [abs_mul, abs_of_nonneg hker]
    exact mul_le_mul_of_nonneg_right (hG d) hker
  have htele := h_telescope_kernel y z hyz
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))
        + (∑ n ∈ Icc 1 z, g n) / (z + 1) - (∑ n ∈ Icc 1 y, g n) / (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
        + |(∑ n ∈ Icc 1 z, g n) / (z + 1)| + |(∑ n ∈ Icc 1 y, g n) / (y + 1)| := by
        set A := ∑ d ∈ Icc (y + 1) z,
          (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1)) with hA
        set B := (∑ n ∈ Icc 1 z, g n) / ((z:ℝ) + 1) with hB
        set C := (∑ n ∈ Icc 1 y, g n) / ((y:ℝ) + 1) with hC
        have h1 : |A + B| ≤ |A| + |B| := abs_add_le A B
        have h2 : |A + B - C| ≤ |A + B| + |C| := by
          rw [sub_eq_add_neg]
          have := abs_add_le (A + B) (-C)
          rwa [abs_neg] at this
        linarith [h1, h2]
    _ ≤ (q * ((1:ℝ) / (y + 1) - 1 / (z + 1))) + q / (z + 1) + q / (y + 1) := by
        have hs : |∑ d ∈ Icc (y + 1) z,
            (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
            ≤ q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) := by
          calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
              ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d ∈ Icc (y + 1) z, q * ((1 : ℝ) / d - 1 / (d + 1)) :=
                Finset.sum_le_sum hterm
            _ = q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) := by
                rw [← Finset.mul_sum, htele]
        have hz1 : |(∑ n ∈ Icc 1 z, g n) / ((z:ℝ) + 1)| ≤ q / (z + 1) := by
          rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (z:ℝ) + 1)]
          apply div_le_div_of_nonneg_right (hG z) (by positivity)
        have hy1 : |(∑ n ∈ Icc 1 y, g n) / ((y:ℝ) + 1)| ≤ q / (y + 1) := by
          rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (y:ℝ) + 1)]
          apply div_le_div_of_nonneg_right (hG y) (by positivity)
        linarith [hs, hz1, hy1]
    _ ≤ 2 * q / (y + 1) := by
        have hzq : (0:ℝ) ≤ q / (z + 1) := by positivity
        have h1 : q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) + q / (z + 1) = q / (y + 1) := by
          field_simp
          ring
        have h2 : q / ((y:ℝ) + 1) + q / (y + 1) = 2 * q / (y + 1) := by ring
        linarith [h1, h2]

/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/


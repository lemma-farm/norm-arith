module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_13023611c61c18cccda8_GoldbachSW2 ====
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

/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/


set_option linter.unusedVariables false in
/-- **The second-order Euler–Maclaurin kernel bound** (Siegel brick A2h-ii-α), in the
    `(s−1)`-cleared form: for `n ≥ 2`, `‖1−s‖ ≤ W`, `W/n ≤ 1`:
    `‖(s−1)n^{−s} − (n^{1−s} − (n+1)^{1−s})‖ ≤ 4(W+1)²·n^{−2}·n^{1−Re s}`. -/
lemma euler_maclaurin_kernel (s : ℂ) (n : ℕ) (hn2 : 2 ≤ n)
    (W : ℝ) (hW : ‖1 - s‖ ≤ W) (hWn : W * (1 / n) ≤ 1) 
    (h_cpow_taylor_two : ∀ (w : ℂ) (z : ℝ),
      0 ≤ z →
        z ≤ 1 / 2 →
          ∀ (W : ℝ),
            ‖w‖ ≤ W → W * z ≤ 1 → ‖(↑(1 + z) : ℂ) ^ w - 1 - w * (↑z : ℂ)‖ ≤ 4 * (W + 1) ^ 2 * z ^ 2)
    :
    ‖(s - 1) * ((n:ℂ)) ^ (-s) - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))‖
      ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - s.re) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hnc0 : ((n:ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hz1 : (1:ℝ) / n ≤ 1/2 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    push_cast
    linarith [show (2:ℝ) ≤ (n:ℝ) from by exact_mod_cast hn2]
  have hz0 : (0:ℝ) ≤ 1 / n := by positivity
  -- (n+1)^{1−s} = n^{1−s}·(1+1/n)^{1−s}
  have hsplit : (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)
      = ((n:ℂ)) ^ ((1:ℂ) - s) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) := by
    have hy0 : (0:ℝ) ≤ 1 + 1/(n:ℝ) := by positivity
    have hb : (((n + 1 : ℕ):ℂ)) = (((n:ℝ) : ℂ)) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) := by
      push_cast
      field_simp
    rw [hb, Complex.mul_cpow_ofReal_nonneg hn0.le hy0]
    norm_cast
  rw [hsplit]
  -- factor: LHS = n^{1−s}·[(1+1/n)^{1−s} − 1 − (1−s)(1/n)]
  have hpow : ((n:ℂ)) ^ ((1:ℂ) - s) = ((n:ℂ)) * ((n:ℂ)) ^ (-s) := by
    rw [show (1:ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hnc0, Complex.cpow_one]
  have hnz : ((n:ℂ)) * ((1/(n:ℝ) : ℝ) : ℂ) = 1 := by
    have hc : ((1/(n:ℝ) : ℝ) : ℂ) = 1 / ((n:ℂ)) := by push_cast; ring
    rw [hc, mul_one_div, div_self hnc0]
  have hfactor : (s - 1) * ((n:ℂ)) ^ (-s)
      - (((n:ℂ)) ^ ((1:ℂ) - s) - ((n:ℂ)) ^ ((1:ℂ) - s) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s))
      = ((n:ℂ)) ^ ((1:ℂ) - s)
        * ((((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) - 1 - ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)) := by
    rw [hpow]
    linear_combination (((1:ℂ) - s) * ((n:ℂ)) ^ (-s)) * hnz
  rw [hfactor, norm_mul]
  have hnorm1 : ‖((n:ℂ)) ^ ((1:ℂ) - s)‖ = ((n:ℝ)) ^ (1 - s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp [Complex.sub_re]
  rw [hnorm1]
  have hbr := h_cpow_taylor_two ((1:ℂ) - s) (1/(n:ℝ)) hz0 hz1 W hW hWn
  calc ((n:ℝ)) ^ (1 - s.re)
        * ‖(((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) - 1 - ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)‖
      ≤ ((n:ℝ)) ^ (1 - s.re) * (4 * (W + 1) ^ 2 * (1/(n:ℝ)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
        have hcast : ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)
            = ((1:ℂ) - s) * (1/(n:ℝ) : ℝ) := by norm_num
        rw [hcast]
        exact hbr
    _ = 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - s.re) := by ring


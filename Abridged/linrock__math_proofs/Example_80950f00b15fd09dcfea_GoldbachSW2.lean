module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_80950f00b15fd09dcfea_GoldbachSW2 ====
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
/-- **Second-order cpow Taylor bound** (Siegel brick A2h-i): for `w : ℂ` and real
    `0 ≤ z ≤ 1/2` with `‖w‖ ≤ W` and `W*z ≤ 1`,
    `‖(1+z)^w − 1 − wz‖ ≤ 4(W+1)²z²` — the engine of the ζ-truncation defect. -/
lemma cpow_taylor_two (w : ℂ) (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1/2)
    (W : ℝ) (hW : ‖w‖ ≤ W) (hWz : W * z ≤ 1) 
    (h_log_taylor_remainder : ∀ (z : ℝ), 0 ≤ z → z ≤ 1 / 2 → |Real.log (1 + z) - z| ≤ z ^ 2)
    :
    ‖((1 + z : ℝ) : ℂ) ^ w - 1 - w * z‖ ≤ 4 * (W + 1) ^ 2 * z ^ 2 := by
  have hW0 : 0 ≤ W := le_trans (norm_nonneg w) hW
  have h1z : (0:ℝ) < 1 + z := by linarith
  -- (1+z)^w = exp(w log(1+z))
  have hcpow : ((1 + z : ℝ) : ℂ) ^ w = Complex.exp (w * Real.log (1 + z)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt h1z)]
    congr 1
    rw [Complex.ofReal_log h1z.le]
    ring
  rw [hcpow]
  -- split: exp(wL) − 1 − wz = [exp(wL) − 1 − wL] + w(L − z)
  set L : ℝ := Real.log (1 + z) with hL
  have hLz : |L - z| ≤ z ^ 2 := h_log_taylor_remainder z h0 h1
  have hLb : |L| ≤ z := by
    have h2 : 0 ≤ L := Real.log_nonneg (by linarith)
    have h3 : L ≤ z := by
      have := Real.log_le_sub_one_of_pos h1z
      rw [hL]
      linarith
    rw [abs_of_nonneg h2]
    exact h3
  have hwL : ‖w * (L : ℂ)‖ ≤ W * z := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul hW hLb (abs_nonneg _) hW0
  -- ‖exp(u) − 1 − u‖ ≤ ‖u‖² for ‖u‖ ≤ 1
  have hexp2 : ‖Complex.exp (w * L) - 1 - w * L‖ ≤ ‖w * (L : ℂ)‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := w * (L : ℂ)) (by
      calc ‖w * (L : ℂ)‖ ≤ W * z := hwL
        _ ≤ 1 := hWz)
    exact this
  have hsplit : Complex.exp (w * L) - 1 - w * z
      = (Complex.exp (w * L) - 1 - w * L) + w * ((L : ℂ) - z) := by
    ring
  rw [hsplit]
  have hterm2 : ‖w * ((L : ℂ) - z)‖ ≤ W * z ^ 2 := by
    rw [norm_mul, show ((L : ℂ) - (z : ℝ)) = (((L - z : ℝ)) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hW hLz (abs_nonneg _) hW0
  have hsq : ‖w * (L : ℂ)‖ ^ 2 ≤ (W * z) ^ 2 := by
    have h := norm_nonneg (w * (L : ℂ))
    nlinarith [hwL, h]
  calc ‖(Complex.exp (w * L) - 1 - w * L) + w * ((L : ℂ) - z)‖
      ≤ ‖Complex.exp (w * L) - 1 - w * L‖ + ‖w * ((L : ℂ) - z)‖ := norm_add_le _ _
    _ ≤ ‖w * (L : ℂ)‖ ^ 2 + W * z ^ 2 := add_le_add hexp2 hterm2
    _ ≤ (W * z) ^ 2 + W * z ^ 2 := by linarith [hsq]
    _ ≤ 4 * (W + 1) ^ 2 * z ^ 2 := by
        nlinarith [hW0, sq_nonneg z, sq_nonneg W, mul_nonneg hW0 (sq_nonneg z)]


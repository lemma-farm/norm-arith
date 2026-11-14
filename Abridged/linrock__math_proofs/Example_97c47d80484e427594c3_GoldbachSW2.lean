module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_97c47d80484e427594c3_GoldbachSW2 ====
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

/-- The bare real-valued function of a quadratic Dirichlet character (A3-d0). -/
noncomputable def charFn (q : ℕ) (χ : DirichletCharacter ℂ q) : ℕ → ℝ :=
  fun n => (χ ((n : ZMod q))).re


set_option linter.unusedVariables false in
/-- **The head difference across the window** (Siegel brick S2c): moving the
    exponent from `β` to `1` across a window with `N^{1−β} ≤ 2` costs only
    `2(1−β)(1+log N)²` on partial sums of a quadratic character. -/
lemma char_head_diff_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (N : ℕ) (hN : 1 ≤ N) {β : ℝ} (hβ1 : 0 < β) (hβ2 : β < 1)
    (hN2 : ((N:ℝ)) ^ (1 - β) ≤ 2) 
    (h_charFn_bound : ∀ {q : ℕ} (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → ∀ (n : ℕ), |charFn q χ n| ≤ 1)
    (h_sum_one_div_le_log : ∀ (z : ℕ), 1 ≤ z → ∑ c ∈ Finset.Icc 1 z, 1 / (↑c : ℝ) ≤ 1 + Real.log (↑z : ℝ))
    :
    |∑ d ∈ Icc 1 N, charFn q χ d / d - ∑ d ∈ Icc 1 N, charFn q χ d * ((d:ℝ)) ^ (-β)|
    ≤ 2 * (1 - β) * (1 + Real.log N) ^ 2 := by
  have hNr : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg hNr
  -- per-term bound
  have hterm : ∀ d : ℕ, d ∈ Icc 1 N →
      |charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)|
      ≤ 2 * (1 - β) * (Real.log d / d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1r : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd.1
    have hd0 : (0:ℝ) < (d:ℝ) := by linarith
    have hlogd : (0:ℝ) ≤ Real.log d := Real.log_nonneg hd1r
    -- factor: 1/d − d^{−β} = −d^{−1}(d^{1−β} − 1)
    have hfac : charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)
        = -(charFn q χ d * (((d:ℝ)) ^ (1 - β) - 1) / d) := by
      have hrw : ((d:ℝ)) ^ (-β) = ((d:ℝ)) ^ (1 - β) / d := by
        rw [eq_div_iff (ne_of_gt hd0)]
        calc ((d:ℝ)) ^ (-β) * (d:ℝ) = ((d:ℝ)) ^ (-β) * ((d:ℝ)) ^ (1:ℝ) := by
              rw [Real.rpow_one]
          _ = ((d:ℝ)) ^ (-β + 1) := (Real.rpow_add hd0 _ _).symm
          _ = ((d:ℝ)) ^ (1 - β) := by ring_nf
      rw [hrw]
      field_simp
      ring
    rw [hfac, abs_neg, abs_div, Nat.abs_cast, abs_mul]
    -- d^{1−β} − 1 ≤ 2(1−β)log d
    have hexp : ((d:ℝ)) ^ (1 - β) - 1 ≤ 2 * (1 - β) * Real.log d := by
      have h1β : (0:ℝ) ≤ 1 - β := by linarith
      have hx0 : (0:ℝ) ≤ (1 - β) * Real.log d := mul_nonneg h1β hlogd
      have hrpow : ((d:ℝ)) ^ (1 - β) = Real.exp ((1 - β) * Real.log d) := by
        rw [Real.rpow_def_of_pos hd0]
        ring_nf
      have hEM : Real.exp ((1 - β) * Real.log d) - 1
          ≤ ((1 - β) * Real.log d) * Real.exp ((1 - β) * Real.log d) := by
        set x : ℝ := (1 - β) * Real.log d with hx
        have h1 := Real.add_one_le_exp (-x)
        have h2 : (0:ℝ) < Real.exp x := Real.exp_pos _
        have h3 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
        rw [h3] at h1
        have h4 : (-x + 1) * Real.exp x ≤ 1 := by
          calc (-x + 1) * Real.exp x ≤ (Real.exp x)⁻¹ * Real.exp x := by
                apply mul_le_mul_of_nonneg_right h1 h2.le
            _ = 1 := inv_mul_cancel₀ (ne_of_gt h2)
        nlinarith [h4]
      have hd2 : ((d:ℝ)) ^ (1 - β) ≤ 2 := by
        calc ((d:ℝ)) ^ (1 - β) ≤ ((N:ℝ)) ^ (1 - β) := by
              apply Real.rpow_le_rpow hd0.le _ h1β
              exact_mod_cast hd.2
          _ ≤ 2 := hN2
      calc ((d:ℝ)) ^ (1 - β) - 1
          = Real.exp ((1 - β) * Real.log d) - 1 := by rw [hrpow]
        _ ≤ ((1 - β) * Real.log d) * Real.exp ((1 - β) * Real.log d) := hEM
        _ = ((1 - β) * Real.log d) * ((d:ℝ)) ^ (1 - β) := by rw [hrpow]
        _ ≤ ((1 - β) * Real.log d) * 2 := by
            apply mul_le_mul_of_nonneg_left hd2 hx0
        _ = 2 * (1 - β) * Real.log d := by ring
    have hnn : (0:ℝ) ≤ ((d:ℝ)) ^ (1 - β) - 1 := by
      have : (1:ℝ) ≤ ((d:ℝ)) ^ (1 - β) := Real.one_le_rpow hd1r (by linarith)
      linarith
    calc |charFn q χ d| * |((d:ℝ)) ^ (1 - β) - 1| / (d:ℝ)
        ≤ 1 * (2 * (1 - β) * Real.log d) / (d:ℝ) := by
          apply div_le_div_of_nonneg_right _ hd0.le
          apply mul_le_mul (h_charFn_bound χ hχ2 d) _ (abs_nonneg _) zero_le_one
          rw [abs_of_nonneg hnn]
          exact hexp
      _ = 2 * (1 - β) * (Real.log d / d) := by ring
  -- sum the per-term bounds
  have hsum : ∑ d ∈ Icc 1 N, Real.log d / d ≤ (1 + Real.log N) ^ 2 := by
    calc ∑ d ∈ Icc 1 N, Real.log d / d
        ≤ ∑ d ∈ Icc 1 N, Real.log N * (1 / d) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hd0 : (0:ℝ) < (d:ℝ) := by
            have : (0:ℕ) < d := by omega
            exact_mod_cast this
          have hlog_le : Real.log d ≤ Real.log N := by
            apply Real.log_le_log hd0
            exact_mod_cast hd.2
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right hlog_le hd0.le
      _ = Real.log N * ∑ d ∈ Icc 1 N, (1:ℝ) / d := by rw [Finset.mul_sum]
      _ ≤ Real.log N * (1 + Real.log N) := by
          apply mul_le_mul_of_nonneg_left (h_sum_one_div_le_log N hN) hlogN
      _ ≤ (1 + Real.log N) ^ 2 := by nlinarith [hlogN]
  calc |∑ d ∈ Icc 1 N, charFn q χ d / d - ∑ d ∈ Icc 1 N, charFn q χ d * ((d:ℝ)) ^ (-β)|
      = |∑ d ∈ Icc 1 N, (charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β))| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ d ∈ Icc 1 N, |charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N, 2 * (1 - β) * (Real.log d / d) := Finset.sum_le_sum hterm
    _ = 2 * (1 - β) * ∑ d ∈ Icc 1 N, Real.log d / d := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 - β) * (1 + Real.log N) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsum
        nlinarith [hβ2]

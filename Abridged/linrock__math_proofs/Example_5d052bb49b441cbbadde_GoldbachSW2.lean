module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_5d052bb49b441cbbadde_GoldbachSW2 ====
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
/-- **The √-size partial sums against `d^{−s}` decay at the `1/√y` rate, uniformly
    in `s ∈ [1,2]`** (Siegel brick A5-d1) — the convolution-side twin of
    `char_rpow_tail_rate`, powering the `Lk` identification. -/
lemma conv_rpow_tail_rate (k : ℕ → ℝ) (B : ℝ)
    (hK : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k n| ≤ B * (Real.sqrt t + 1))
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (y : ℕ) (hy1 : 1 ≤ y) 
    (h_sum_three_half_tail_sharp : ∀ (y : ℕ),
      1 ≤ y →
        ∀ (z : ℕ),
          y ≤ z → ∑ d ∈ Finset.Icc (y + 1) z, 1 / ((↑d : ℝ) * √(↑d : ℝ)) ≤ 2 / √(↑y : ℝ) - 2 / √(↑z : ℝ))
    (h_rpow_diff_le : ∀ (n : ℕ),
      1 ≤ n → ∀ (σ : ℝ), 0 ≤ σ → (↑n : ℝ) ^ (-σ) - (↑(n + 1) : ℝ) ^ (-σ) ≤ σ * (↑n : ℝ) ^ (-σ - 1))
    :
    ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, k d * ((d:ℝ)) ^ (-s)| ≤ 30 * B / Real.sqrt y := by
  have hB0 : 0 ≤ B := by
    have h0 := hK 0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero,
      Nat.cast_zero, Real.sqrt_zero, zero_add, mul_one] at h0
    exact h0
  set w : ℕ → ℝ := fun d => ((d:ℝ)) ^ (-s) with hw
  -- the Abel window identity (generic in w)
  have hwindow : ∀ z : ℕ, y ≤ z →
      ∑ d ∈ Icc (y + 1) z, k d * w d
      = ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, k n) * w (z + 1) - (∑ n ∈ Icc 1 y, k n) * w (y + 1) := by
    intro z
    induction z with
    | zero =>
      intro hy0
      omega
    | succ m ih =>
      intro hym
      rcases Nat.lt_or_ge m y with hlt | hge
      · have hy' : y = m + 1 := by omega
        subst hy'
        have hempty : Icc (m + 1 + 1) (m + 1) = (∅ : Finset ℕ) :=
          Finset.Icc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty, Finset.sum_empty]
        ring
      · have hins : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
          ext d
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        have hnotmem : (m + 1) ∉ Icc (y + 1) m := by
          simp only [Finset.mem_Icc]
          omega
        rw [hins, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, ih hge]
        have hS : ∑ n ∈ Icc 1 (m + 1), k n = k (m + 1) + ∑ n ∈ Icc 1 m, k n := by
          rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) from by
            ext d
            simp only [Finset.mem_insert, Finset.mem_Icc]
            omega, Finset.sum_insert (by
              simp only [Finset.mem_Icc]
              omega)]
        rw [hS]
        ring
  -- per-term kernel bound: |S d|(w d − w(d+1)) ≤ 4B/(d√d) for d ≥ 1
  have hkernel : ∀ d : ℕ, 1 ≤ d →
      |(∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))| ≤ 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by
    intro d hd
    have hd0 : (0:ℝ) < (d:ℝ) := by
      have : (0:ℕ) < d := hd
      exact_mod_cast this
    have hd1r : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hsq1 : (1:ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1r
    have hΔ0 : 0 ≤ w d - w (d + 1) := by
      rw [hw]
      simp only
      have : (((d + 1 : ℕ)):ℝ) ^ (-s) ≤ ((d:ℝ)) ^ (-s) := by
        apply Real.rpow_le_rpow_of_nonpos hd0 (by push_cast; linarith)
        linarith
      push_cast at this ⊢
      linarith
    have hΔle : w d - w (d + 1) ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
      rw [hw]
      simp only
      have h1 := h_rpow_diff_le d hd s (by linarith)
      have h2 : ((d:ℝ)) ^ (-s - 1) ≤ ((d:ℝ)) ^ (-(2:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hd1r
        linarith
      have h3 : s * ((d:ℝ)) ^ (-s - 1) ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
        calc s * ((d:ℝ)) ^ (-s - 1) ≤ 2 * ((d:ℝ)) ^ (-s - 1) := by
              apply mul_le_mul_of_nonneg_right hs2 (Real.rpow_nonneg hd0.le _)
          _ ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
              apply mul_le_mul_of_nonneg_left h2 (by norm_num)
      push_cast at h1 ⊢
      linarith
    have hSb : |∑ n ∈ Icc 1 d, k n| ≤ 2 * B * Real.sqrt d := by
      calc |∑ n ∈ Icc 1 d, k n| ≤ B * (Real.sqrt d + 1) := hK d
        _ ≤ B * (Real.sqrt d + Real.sqrt d) := by
            apply mul_le_mul_of_nonneg_left _ hB0
            linarith
        _ = 2 * B * Real.sqrt d := by ring
    have hrpow2 : ((d:ℝ)) ^ (-(2:ℝ)) = 1 / ((d:ℝ) * (d:ℝ)) := by
      rw [show (-(2:ℝ)) = -(((2:ℕ)):ℝ) from by norm_num, Real.rpow_neg hd0.le,
        Real.rpow_natCast, pow_two, one_div]
    have hcollect : Real.sqrt d * (1 / ((d:ℝ) * (d:ℝ))) = 1 / ((d:ℝ) * Real.sqrt d) := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), one_mul]
      calc Real.sqrt d * ((d:ℝ) * Real.sqrt d)
          = (Real.sqrt d * Real.sqrt d) * (d:ℝ) := by ring
        _ = (d:ℝ) * (d:ℝ) := by rw [Real.mul_self_sqrt hd0.le]
    rw [abs_mul, abs_of_nonneg hΔ0]
    calc |∑ n ∈ Icc 1 d, k n| * (w d - w (d + 1))
        ≤ (2 * B * Real.sqrt d) * (2 * ((d:ℝ)) ^ (-(2:ℝ))) := by
          apply mul_le_mul hSb hΔle hΔ0
          positivity
      _ = 4 * B * (Real.sqrt d * ((d:ℝ)) ^ (-(2:ℝ))) := by ring
      _ = 4 * B * (Real.sqrt d * (1 / ((d:ℝ) * (d:ℝ)))) := by rw [hrpow2]
      _ = 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by rw [hcollect]
  intro z hz
  rw [hwindow z hz]
  have hy0 : (0:ℝ) < (y:ℝ) := by
    have : (0:ℕ) < y := hy1
    exact_mod_cast this
  have hz0 : (0:ℝ) < (z:ℝ) := by
    have : (0:ℕ) < z := by omega
    exact_mod_cast this
  have hsqy : (1:ℝ) ≤ Real.sqrt y := Real.one_le_sqrt.mpr (by exact_mod_cast hy1)
  have hsqy0 : (0:ℝ) < Real.sqrt y := by linarith
  have hsqz0 : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.mpr hz0
  -- the three pieces
  have h1 : |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
      ≤ 8 * B / Real.sqrt y := by
    calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
        ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc (y + 1) z, 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          exact hkernel d (by omega)
      _ = 4 * B * ∑ d ∈ Icc (y + 1) z, (1 : ℝ) / (d * Real.sqrt d) := by
          rw [Finset.mul_sum]
      _ ≤ 4 * B * (2 / Real.sqrt y - 2 / Real.sqrt z) := by
          apply mul_le_mul_of_nonneg_left (h_sum_three_half_tail_sharp y hy1 z hz)
            (by positivity)
      _ ≤ 8 * B / Real.sqrt y := by
          have h3 : (0:ℝ) ≤ 4 * B * (2 / Real.sqrt z) := by positivity
          have heq : 4 * B * (2 / Real.sqrt y - 2 / Real.sqrt z)
              = 8 * B / Real.sqrt y - 4 * B * (2 / Real.sqrt z) := by ring
          linarith [heq.le, heq.ge]
  have hwle : ∀ t : ℕ, 1 ≤ t → w (t + 1) ≤ 1 / (t:ℝ) := by
    intro t ht
    have ht0 : (0:ℝ) < (t:ℝ) := by
      have : (0:ℕ) < t := ht
      exact_mod_cast this
    have ht1 : (1:ℝ) ≤ ((t + 1 : ℕ):ℝ) := by push_cast; linarith
    rw [hw]
    simp only
    calc ((t + 1 : ℕ):ℝ) ^ (-s) ≤ ((t + 1 : ℕ):ℝ) ^ (-(1:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      _ = 1 / ((t + 1 : ℕ):ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / (t:ℝ) := by
          apply one_div_le_one_div_of_le ht0
          push_cast
          linarith
  have hbz : |(∑ n ∈ Icc 1 z, k n) * w (z + 1)| ≤ 2 * B / Real.sqrt y := by
    have hw0z : 0 ≤ w (z + 1) := by
      rw [hw]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsqzz : Real.sqrt z / (z:ℝ) = 1 / Real.sqrt z := by
      rw [eq_div_iff (ne_of_gt hsqz0)]
      field_simp
      exact Real.sq_sqrt hz0.le
    calc |(∑ n ∈ Icc 1 z, k n) * w (z + 1)|
        = |∑ n ∈ Icc 1 z, k n| * w (z + 1) := by rw [abs_mul, abs_of_nonneg hw0z]
      _ ≤ (2 * B * Real.sqrt z) * (1 / (z:ℝ)) := by
          apply mul_le_mul _ (hwle z (by omega)) hw0z (by positivity)
          calc |∑ n ∈ Icc 1 z, k n| ≤ B * (Real.sqrt z + 1) := hK z
            _ ≤ B * (Real.sqrt z + Real.sqrt z) := by
                apply mul_le_mul_of_nonneg_left _ hB0
                have : (1:ℝ) ≤ Real.sqrt z := Real.one_le_sqrt.mpr (by
                  have : (1:ℕ) ≤ z := by omega
                  exact_mod_cast this)
                linarith
            _ = 2 * B * Real.sqrt z := by ring
      _ = 2 * B * (Real.sqrt z / (z:ℝ)) := by ring
      _ = 2 * B * (1 / Real.sqrt z) := by rw [hsqzz]
      _ ≤ 2 * B / Real.sqrt y := by
          rw [mul_one_div]
          apply div_le_div_of_nonneg_left (by linarith) hsqy0
          exact Real.sqrt_le_sqrt (by exact_mod_cast hz)
  have hby : |(∑ n ∈ Icc 1 y, k n) * w (y + 1)| ≤ 2 * B / Real.sqrt y := by
    have hw0y : 0 ≤ w (y + 1) := by
      rw [hw]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsqyy : Real.sqrt y / (y:ℝ) = 1 / Real.sqrt y := by
      rw [eq_div_iff (ne_of_gt hsqy0)]
      field_simp
      exact Real.sq_sqrt hy0.le
    calc |(∑ n ∈ Icc 1 y, k n) * w (y + 1)|
        = |∑ n ∈ Icc 1 y, k n| * w (y + 1) := by rw [abs_mul, abs_of_nonneg hw0y]
      _ ≤ (2 * B * Real.sqrt y) * (1 / (y:ℝ)) := by
          apply mul_le_mul _ (hwle y hy1) hw0y (by positivity)
          calc |∑ n ∈ Icc 1 y, k n| ≤ B * (Real.sqrt y + 1) := hK y
            _ ≤ B * (Real.sqrt y + Real.sqrt y) := by
                apply mul_le_mul_of_nonneg_left _ hB0
                linarith
            _ = 2 * B * Real.sqrt y := by ring
      _ = 2 * B * (Real.sqrt y / (y:ℝ)) := by ring
      _ = 2 * B * (1 / Real.sqrt y) := by rw [hsqyy]
      _ = 2 * B / Real.sqrt y := by rw [mul_one_div]
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, k n) * w (z + 1) - (∑ n ∈ Icc 1 y, k n) * w (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
        + |(∑ n ∈ Icc 1 z, k n) * w (z + 1)| + |(∑ n ∈ Icc 1 y, k n) * w (y + 1)| := by
        have ha := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
          + (∑ n ∈ Icc 1 z, k n) * w (z + 1)) (-((∑ n ∈ Icc 1 y, k n) * w (y + 1)))
        have hb := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1)))
          ((∑ n ∈ Icc 1 z, k n) * w (z + 1))
        rw [abs_neg, ← sub_eq_add_neg] at ha
        linarith
    _ ≤ 8 * B / Real.sqrt y + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y := by
        linarith [h1, hbz, hby]
    _ ≤ 30 * B / Real.sqrt y := by
        have h30 : (12:ℝ) * B / Real.sqrt y ≤ 30 * B / Real.sqrt y := by
          apply div_le_div_of_nonneg_right _ hsqy0.le
          linarith
        have heq : 8 * B / Real.sqrt y + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y
            = 12 * B / Real.sqrt y := by ring
        linarith [heq.le, heq.ge, h30]

